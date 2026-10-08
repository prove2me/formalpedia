-- Prove2me | Theorems.Thm_FixpNash_WeakApprox_first_case_sum_lt
-- name    : FixpNash.WeakApprox.first_case_sum_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:12.795842+00:00
-- url     : https://prove2.me/theorems/36b00c24-b247-45e0-ab8a-d6788c65cd69
-- title:
--   Proof of Proposition 3, p. 21 — first case: g_{i,j} < 0 and x_{i,j} ≥ ε/2cn² force Σ_l φ_{i,l} < ε
-- statement:
--   Let $\Gamma$, $n$, $c$, $0<\varepsilon\le1$, $\varepsilon'=\varepsilon^2/(4c^2n^3)$ and $\varphi_{i,j}=\max\{0,g_{i,j}\}$ be as in the coordinatewise bound, and let $x$ be a weak $\varepsilon'$-approximate fixed point of Nash's function. If, for a player $i$, some strategy $j\in S_i$ has negative gain $g_{i,j}(x)<0$ and probability
--   $$x_{i,j}\ge\frac{\varepsilon}{2cn^2},$$
--   then
--   $$\sum_{l\in S_i}\varphi_{i,l}(x)<\varepsilon.$$
--
--   This is the first of the two cases into which the paper splits the end of the proof of Proposition 3; it bounds every positive gain of player $i$ by $\varepsilon$ at once.
--
--   **Formalization Note** "One of the strategies $j$ on the rhs" means $\psi_{i,j}(x)>0$, i.e. $g_{i,j}(x)<0$, which is the hypothesis used. $\epsilon/2cn^2$ is read as $\varepsilon/(2cn^2)$.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Proposition 3, second direction, first case, p. 21

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_WeakApprox_NashFunction
import Definitions.Def_FixpNash_WeakApprox_GameConstants

namespace FixpNash.WeakApprox

/-- Proof of Proposition 3, p. 21, first case: if some strategy `j` with `g_{i,j}(x) < 0` has
`x_{i,j} ≥ ε/(2cn²)`, then `Σ_l φ_{i,l}(x) < ε`. -/
theorem first_case_sum_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : ∀ i, S i → ℝ)
    (hx : IsWeakApproxFixedPoint u x
      (ε ^ 2 / (4 * cConst u ^ 2 * (maxNumStrategies S : ℝ) ^ 3)))
    (i : ι) (j : S i) (hg : gain u x i j < 0)
    (hxj : ε / (2 * cConst u * (maxNumStrategies S : ℝ) ^ 2) ≤ x i j) :
    ∑ l : S i, max 0 (gain u x i l) < ε := by sorry

end FixpNash.WeakApprox
