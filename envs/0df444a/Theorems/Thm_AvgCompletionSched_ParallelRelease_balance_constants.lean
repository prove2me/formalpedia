-- Prove2me | Theorems.Thm_AvgCompletionSched_ParallelRelease_balance_constants
-- name    : AvgCompletionSched.ParallelRelease.balance_constants
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:58:35.26302+00:00
-- url     : https://prove2.me/theorems/23349e17-1342-4932-b80d-f7a5bfb9c0b3
-- title:
--   The balancing constants: at $\alpha=2\sqrt2-2$, $\beta=\sqrt{3-2\sqrt2}$ both ratios equal $2\sqrt2$
-- statement:
--   Let $\alpha=2\sqrt2-2$ and $\beta=\sqrt{3-2\sqrt2}$. Then
--   $$2+\alpha=2\sqrt2\qquad\text{and}\qquad 2+\beta+\frac{1-\alpha}{\beta}=2\sqrt2.$$
--
--   These are the values at which the list-scheduling ratio $2+\alpha$ and the Delay List ratio $2+\beta+(1-\alpha)/\beta$ (with $\beta=\sqrt{1-\alpha}$) coincide, which gives the ratio $2\sqrt2\approx2.83$ of Lemma 4.19. Note that $1-\alpha=3-2\sqrt2=(\sqrt2-1)^2$, so $\beta=\sqrt2-1$.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 164, proof of Lemma 4.19, second and third paragraphs

import Mathlib

namespace AvgCompletionSched.ParallelRelease

/-- The balancing constants (p. 164): with `α = 2√2 - 2` and `β = √(3 - 2√2)`, both
`2 + α` and `2 + β + (1 - α)/β` equal `2√2`. -/
theorem balance_constants :
    2 + (2 * Real.sqrt 2 - 2) = 2 * Real.sqrt 2 ∧
      2 + Real.sqrt (3 - 2 * Real.sqrt 2) +
          (1 - (2 * Real.sqrt 2 - 2)) / Real.sqrt (3 - 2 * Real.sqrt 2) =
        2 * Real.sqrt 2 := by sorry

end AvgCompletionSched.ParallelRelease
