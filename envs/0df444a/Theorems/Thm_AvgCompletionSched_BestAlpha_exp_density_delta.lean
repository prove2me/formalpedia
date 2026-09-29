-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_exp_density_delta
-- name    : AvgCompletionSched.BestAlpha.exp_density_delta
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:47:16.828985+00:00
-- url     : https://prove2.me/theorems/cd8eae31-5fff-4b19-aa0f-84bccdc230e9
-- title:
--   Proof of Theorem 2.6.3: for $f(\alpha)=e^\alpha/(e-1)$, $\int_0^\beta\frac{1+\alpha-\beta}{\beta}f(\alpha)\,d\alpha=\frac1{e-1}$
-- statement:
--   Let $e$ be Euler's number and $f(\alpha)=e^\alpha/(e-1)$. Then $f$ is a probability density on $(0,1]$: $f\ge0$ and $\int_0^1 f(\alpha)\,d\alpha=1$. Moreover, for every $\beta\in(0,1]$,
--   $$\int_0^\beta \frac{1+\alpha-\beta}{\beta}\cdot\frac{e^\alpha}{e-1}\,d\alpha=\frac{1}{e-1}.$$
--
--   Consequently the quantity $\delta=\max_{0<\beta\le1}\int_0^\beta\frac{1+\alpha-\beta}{\beta}f(\alpha)\,d\alpha$ of Lemma 2.5 equals $1/(e-1)$ for this density, and $1+\delta=e/(e-1)$. This is the calculation behind the $e/(e-1)\approx1.58$ bound of Theorem 2.6, part 3.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, pp. 154–155, §2, proof of Theorem 2.6, part 3 (displays)

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem exp_density_delta :
    (∀ α : ℝ, 0 ≤ Real.exp α / (Real.exp 1 - 1)) ∧
      ∫ α in (0 : ℝ)..1, Real.exp α / (Real.exp 1 - 1) = 1 ∧
      ∀ β ∈ Set.Ioc (0 : ℝ) 1,
        ∫ α in (0 : ℝ)..β, (1 + α - β) / β * (Real.exp α / (Real.exp 1 - 1))
          = 1 / (Real.exp 1 - 1) := by sorry
end AvgCompletionSched.BestAlpha
