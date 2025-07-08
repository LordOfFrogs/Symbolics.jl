using Symbolics

δ(k) = ifelse(isequal(k, 0), 1 : 0)
@register_symbolic δ(k)

Σ(expr, n, startidx, endidx) = sum(substitute(expr, Dict(n => i)) for i in startidx:endidx)
Π(expr, n, startidx, endidx) = prod(substitute(expr, Dict(n => i)) for i in startidx:endidx)
@register_symbolic Σ(expr, n, startidx, endidx)
@register_symbolic Π(expr, n, startidx, endidx)

@register_symbolic DTM(expr, k)
"""
Differential Transform Method from [this paper](https://www.researchgate.net/publication/267767445_A_New_Algorithm_for_Solving_Linear_Ordinary_Differential_Equations)
"""
function DTM(expr, x, k, y, Y)
    if expr isa Equation
        return DTM(expr.lhs, x, k, y, Y) ~ DTM(expr.rhs, x, k, y, Y)
    end

    @variables n, m
    simple_rules = Symbolics.Chain([
        @rule 1 => δ(k)
        @rule x => δ(k - 1)
        @rule x^(~m) => δ(k - ~m)
        @rule exp(~λ * x) => (~λ)^k / factorial(k)
        @acrule (1 + x)^(~m) => Π(~m - n, n, 0, k-1) / factorial(k)
    ])

    if !isequal(simple_rules(expr), expr)
        return simple_rules(expr)
    end

    terms = Symbolics.terms(expr)

    # DTM(g(x) + h(x)) = DTM(g(x)) + DTM(h(x))
    if length(terms) > 1
        return sum(DTM(term, x, k, y, Y) for term in terms)
    end

    facs = Symbolics.factors(expr)
    const_fac = filter(fac -> isempty(Symbolics.get_variables(fac)), facs)
    nonconst_fac = filter(fac -> !isempty(Symbolics.get_variables(fac)), facs)

    # DTM(g(x)*h(x)) = Σ(m=0:k)( H(m) * G(k - m) )
    if length(nonconst_fac) >= 2
        g, h = nonconst_fac[1], nonconst_fac[2]
        G, H = DTM(g, x, k, y, Y), DTM(h, x, k, y, Y)
        x_pow = Symbolics.Chain([
            @rule x^~m => (true, ~m)
            @rule x => (true, 1)
            @rule ~x::(a -> !(a isa Tuple)) => (false, 0)
        ])
        if x_pow(g)[1]
            transformed = ifelse(k >= x_pow(g)[2], substitute(H, Dict(k => k - x_pow(g)[2])), 0)
        elseif x_pow(h)[1]
            transformed = ifelse(k >= x_pow(h)[2], substitute(G, Dict(k => k - x_pow(h)[2])), 0)
        else
            transformed = Σ(substitute(H, Dict(k => m)) * substitute(G, Dict(k => k - m)), m, 0, k)
        end
        return prod(const_fac) * transformed * (length(nonconst_fac) > 2 ? DTM(prod(nonconst_fac[3:end]), x, k, y, Y) : 1)
    end

    if !isempty(const_fac) || length(nonconst_fac) >= 2
        # DTM(α * g(x)) = α * DTM(g(x))
        return prod(const_fac) * DTM(prod(nonconst_fac), x, k, y, Y)
    end

    Dx = Differential(x)
    order, inside_expr = unwrap_der(expr, Dx)
    if order > 0
        return prod(k + n for n = 1:order)*DTM(inside_expr, x, k + order, y, Y)
    end

    if isequal(expr, y)
        return Y(k)
    end
    
    return DTM(expr, k)
end

function unwrap_der(expr, Dt)
    reduce_rule = @rule Dt(~x) => ~x

    if reduce_rule(expr) === nothing
        return 0, expr
    end

    order, expr = unwrap_der(reduce_rule(expr), Dt)
    return order + 1, expr
end