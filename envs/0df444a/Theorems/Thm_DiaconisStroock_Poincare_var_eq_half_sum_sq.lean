-- Prove2me | Theorems.Thm_DiaconisStroock_Poincare_var_eq_half_sum_sq
-- name    : DiaconisStroock.Poincare.var_eq_half_sum_sq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T16:59:49.473818+00:00
-- url     : https://prove2.me/theorems/5ac4a88c-9c8a-4f4d-9a66-83b05cb1619d
-- title:
--   §1B, proof of Proposition 1 — variance as a pairwise sum
-- statement:
--   Let $\pi$ be a probability distribution on a finite set $X$ and $\phi:X\to\mathbb R$. Its variance equals half the average squared difference between two independent draws from $\pi$:
--
--   $$
--   \operatorname{Var}_\pi(\phi)=\frac12\sum_{x,y\in X}(\phi(x)-\phi(y))^2\pi(x)\pi(y).
--   $$
--
--   This is the opening identity in the proof of Proposition 1 and connects the variance to ordered pairs of states.
--
--   **Formalization Note** No transition matrix is needed for this identity; only the probability distribution is assumed.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 38, §1B, proof of Proposition 1, first display, https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_lower

namespace DiaconisStroock.Poincare

open MarkovMixing
open scoped BigOperators

/-- The first equality in the proof of Proposition 1, p. 38. -/
theorem var_eq_half_sum_sq {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : IsDist π) (φ : V → ℝ) :
    distVar π φ = 2⁻¹ * ∑ x, ∑ y, (φ x - φ y) ^ 2 * (π x * π y) := by sorry

end DiaconisStroock.Poincare
