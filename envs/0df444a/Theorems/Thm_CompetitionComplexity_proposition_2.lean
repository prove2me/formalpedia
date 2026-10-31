-- Prove2me | Theorems.Thm_CompetitionComplexity_proposition_2
-- name    : CompetitionComplexity.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:28.402989+00:00
-- url     : https://prove2.me/theorems/3621f3f7-6eae-4107-8484-53fb11bb537c
-- title:
--   Proposition 2 — $\Gamma^\varepsilon_{n,m}$ is convex with unique minimizer $Y$ of (10), and $\Gamma^\varepsilon_{n,m}(Y)=\varepsilon-(n-1)\rho_{\varepsilon,m}^n$
-- statement:
--   Let $\varepsilon>0$, let $n\ge2$ and $m\ge3$ be integers, and assume $\rho_{\varepsilon,m}$ of the recursion (9) is well defined. On the open orthant $\mathbb R^{m-1}_+$ consider
--   $$
--   \Gamma^\varepsilon_{n,m}(x)=\varepsilon+x_1^n+\sum_{i=1}^{m-2}x_i\Bigl(\varepsilon+\Bigl(\frac{x_{i+1}}{x_i}\Bigr)^n\Bigr)-x_{m-1}(n-1-\varepsilon).
--   $$
--   Then:
--
--   1. $\Gamma^\varepsilon_{n,m}$ is convex on $\mathbb R^{m-1}_+$;
--   2. the vector $Y$ given by $Y_1=\rho_{\varepsilon,m}$ and $Y_j=\prod_{k=0}^{j-1}\rho_{\varepsilon,m-k}$ for $j\in\{2,\dots,m-1\}$ lies in $\mathbb R^{m-1}_+$ and minimizes $\Gamma^\varepsilon_{n,m}$ there;
--   3. every minimizer of $\Gamma^\varepsilon_{n,m}$ on $\mathbb R^{m-1}_+$ equals $Y$;
--   4. $\Gamma^\varepsilon_{n,m}(Y)=\varepsilon-(n-1)\rho_{\varepsilon,m}^{\,n}$.
--
--   This solves the finite-dimensional part of the program (1)–(4) in closed form.
--
--   Differences from the source:
--   - encoding: R^{m−1}_+ → the open orthant {x : Fin (m−1) → ℝ | ∀ i, 0 < x i}; reason: Γ divides by xᵢ and the proof places Y in this region by showing it is strictly positive
--   - encoding: a unique minimizer Y → Y minimizes Γ on the orthant, and every minimizer on the orthant equals Y; reason: the definition of a unique minimizer
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Proposition 2, pp.15–16

import Mathlib
import Definitions.Def_CompetitionComplexity_Recursion
import Definitions.Def_CompetitionComplexity_Gamma

namespace CompetitionComplexity

/-- **Proposition 2.**
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Proposition 2, pp.15–16:
"Let ε > 0, and let n ≥ 2 and m ≥ 3 be two positive integers such that ρε,m is well defined. Then,
Γε n,m is convex over R^{m−1}_+ and it has a unique minimizer Y in this region, given by
Y1 = ρε,m and Yj = Π_{k=0}^{j−1} ρε,m−k for every j ∈ {2,...,m−1}. (10)
Furthermore, Γε n,m(Y) = ε − (n − 1)ρ^n_{ε,m}."

Conclusions: `Γ` is convex on the open orthant; `Y` lies in the orthant and minimizes `Γ` there; every
minimizer in the orthant equals `Y`; and `Γ(Y) = ε − (n − 1)ρⁿ_{ε,m}`.

**Formalization Note.** `ℝ^{m−1}_+` is the open orthant (`Γ` divides by `xᵢ`). -/
theorem proposition_2 (ε : ℝ) (hε : 0 < ε) (n m : ℕ) (hn : 2 ≤ n) (hm : 3 ≤ m)
    (hw : WellDef ε n m) :
    ConvexOn ℝ (orthant m) (Gamma ε n m) ∧ Yvec ε n m ∈ orthant m ∧
    (∀ x ∈ orthant m, Gamma ε n m (Yvec ε n m) ≤ Gamma ε n m x) ∧
    (∀ x ∈ orthant m, (∀ z ∈ orthant m, Gamma ε n m x ≤ Gamma ε n m z) → x = Yvec ε n m) ∧
    Gamma ε n m (Yvec ε n m) = ε - ((n : ℝ) - 1) * rho ε n m ^ n := by sorry

end CompetitionComplexity
