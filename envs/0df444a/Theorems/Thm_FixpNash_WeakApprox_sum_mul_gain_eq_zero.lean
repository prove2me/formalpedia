-- Prove2me | Theorems.Thm_FixpNash_WeakApprox_sum_mul_gain_eq_zero
-- name    : FixpNash.WeakApprox.sum_mul_gain_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:23.857429+00:00
-- url     : https://prove2.me/theorems/3cba2f79-b4e3-443d-9b24-a87ecdcf90f8
-- title:
--   Proof of Proposition 3, p. 21 — Σ_j x_{i,j} g_{i,j}(x) = 0
-- statement:
--   Let $\Gamma$ be a finite game and $x$ a mixed profile. For every player $i$, the gains $g_{i,j}(x)=u_i((i{:}j);x_{-i})-u_i(x)$ average to zero under $x_i$:
--   $$\sum_{j\in S_i}x_{i,j}\,g_{i,j}(x)=0.$$
--
--   Splitting the sum by the sign of $g_{i,j}(x)$, with $\varphi_{i,j}=\max\{0,g_{i,j}\}$ and $\psi_{i,j}=-g_{i,j}$ where $g_{i,j}\le0$, gives $\sum x_{i,j}\varphi_{i,j}(x)=\sum x_{i,j}\psi_{i,j}(x)$, the identity on which the second direction of the proof of Proposition 3 is built.
--
--   **Formalization Note** The page writes the sum as $\sum_{j=1}^{m_i}$; it runs over all of $S_i$. $x$ is a mixed profile in the sense of `agt_games`.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Proposition 3, second direction, p. 21

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_WeakApprox_NashFunction

namespace FixpNash.WeakApprox

/-- Proof of Proposition 3, p. 21: for a mixed profile `x` and every player `i`,
`Σ_j x_{i,j} g_{i,j}(x) = 0`. -/
theorem sum_mul_gain_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x) (i : ι) :
    ∑ j : S i, x i j * gain u x i j = 0 := by sorry

end FixpNash.WeakApprox
