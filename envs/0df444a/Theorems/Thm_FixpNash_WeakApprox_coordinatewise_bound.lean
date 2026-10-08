-- Prove2me | Theorems.Thm_FixpNash_WeakApprox_coordinatewise_bound
-- name    : FixpNash.WeakApprox.coordinatewise_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:12.247993+00:00
-- url     : https://prove2.me/theorems/07ed89fb-f28f-4e3d-ae8a-e4d4bdcddd0a
-- title:
--   Proof of Proposition 3, p. 21 — |φ_{i,j} − x_{i,j}Σ_l φ_{i,l}| < ε′(1 + Σ_l φ_{i,l}) < ε²/2cn²
-- statement:
--   Let $\Gamma$ be a finite game with constants $n$ (the maximum number of pure strategies of a player), $M$ (the maximum over players of the spread between their largest and smallest pure payoff) and $c=1+M$. Let $0<\varepsilon\le1$, put
--   $$\varepsilon'=\frac{\varepsilon^2}{4c^2n^3},$$
--   and let $x$ be a weak $\varepsilon'$-approximate fixed point of Nash's function: a mixed profile with $|F_\Gamma(x)-x|_\infty<\varepsilon'$. Write $\varphi_{i,j}(x)=\max\{0,g_{i,j}(x)\}$. Then for every player $i$ and every $j\in S_i$,
--   $$\Bigl|\varphi_{i,j}(x)-x_{i,j}\sum_{l}\varphi_{i,l}(x)\Bigr|<\varepsilon'\Bigl(1+\sum_l\varphi_{i,l}(x)\Bigr)<\frac{\varepsilon^2}{2cn^2},$$
--   where the sums run over $l\in S_i$.
--
--   This turns the approximate fixed-point condition into a bound on each positive gain relative to the total positive gain of the player; the case analysis that concludes the proof of Proposition 3 starts from it.
--
--   **Formalization Note** Both inequalities of the page's chain are stated, as a conjunction. $\varepsilon\le1$ is the page's "Assume without loss of generality that $\epsilon\le1$". $n$ and $c$ are computed from the game (`maxNumStrategies`, `cConst`); $\epsilon^2/2cn^2$ is read as $\varepsilon^2/(2cn^2)$, as the page writes it two lines later.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Proposition 3, second direction, p. 21

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_WeakApprox_NashFunction
import Definitions.Def_FixpNash_WeakApprox_GameConstants

namespace FixpNash.WeakApprox

/-- Proof of Proposition 3, p. 21: with `ε' = ε²/(4c²n³)` and `φ_{i,j} = max{0, g_{i,j}}`, a weak
`ε'`-approximate fixed point satisfies
`|φ_{i,j}(x) - x_{i,j} Σ_l φ_{i,l}(x)| < ε'(1 + Σ_l φ_{i,l}(x)) < ε²/(2cn²)`. -/
theorem coordinatewise_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : ∀ i, S i → ℝ)
    (hx : IsWeakApproxFixedPoint u x
      (ε ^ 2 / (4 * cConst u ^ 2 * (maxNumStrategies S : ℝ) ^ 3))) :
    ∀ (i : ι) (j : S i),
      |max 0 (gain u x i j) - x i j * ∑ l : S i, max 0 (gain u x i l)| <
          ε ^ 2 / (4 * cConst u ^ 2 * (maxNumStrategies S : ℝ) ^ 3) *
            (1 + ∑ l : S i, max 0 (gain u x i l)) ∧
        ε ^ 2 / (4 * cConst u ^ 2 * (maxNumStrategies S : ℝ) ^ 3) *
            (1 + ∑ l : S i, max 0 (gain u x i l)) <
          ε ^ 2 / (2 * cConst u * (maxNumStrategies S : ℝ) ^ 2) := by sorry

end FixpNash.WeakApprox
