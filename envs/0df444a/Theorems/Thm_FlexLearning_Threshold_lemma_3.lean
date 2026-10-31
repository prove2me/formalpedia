-- Prove2me | Theorems.Thm_FlexLearning_Threshold_lemma_3
-- name    : FlexLearning.Threshold.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:43.387679+00:00
-- url     : https://prove2.me/theorems/affd06c6-2e44-408c-812f-da8b2ffc6b70
-- title:
--   Lemma 3, p. A3 — newsvendor with U[x, x+U] demand: Q̄ = x + U(p−c)/p is optimal, with profit (p−c)x + (U/2)(p−c)²/p
-- statement:
--   Consider a newsvendor selling at unit price $p$, buying at unit cost $c$ with $0 \le c < p$, no salvage value, facing demand $D$ uniform on $[x, x+U]$ with $x \ge 0$ and $U > 0$. For a capacity $Q$ the expected profit is $\pi(Q) = \mathbb E[p\min\{D,Q\} - cQ]$. Then the capacity
--   $$\bar Q = x + U\,\frac{p-c}{p} \ \ (\ge 0)$$
--   maximizes $\pi$ over $Q \ge 0$, and its expected profit is
--   $$\pi(\bar Q) = (p-c)x + \frac U2\,\frac{(p-c)^2}{p}.$$
--
--   This closed form is the building block of every optimal profit in the paper: the static non-flexible optimum, and the second-period value after a stock-out, where the posterior demand is again uniform.
--
--   **Formalization Note** The paper allows $U \ge 0$ and any costs; here $U > 0$ (so that the uniform law is a probability measure) and $0 \le c < p$ (nonnegative cost, positive margin) are assumed. The maximizer is not claimed unique: at $c = 0$ every $Q \ge x + U$ is optimal.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), p. A3 (PDF 36), Lemma 3 (first part)

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

namespace FlexLearning.Threshold

theorem lemma_3 (p c x U : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    0 ≤ x + U * ((p - c) / p) ∧
    nvProfit p c (prior x U) (x + U * ((p - c) / p)) = (p - c) * x + U / 2 * ((p - c) ^ 2 / p) ∧
    ∀ Q : ℝ, 0 ≤ Q →
      nvProfit p c (prior x U) Q ≤ nvProfit p c (prior x U) (x + U * ((p - c) / p)) := by sorry

end FlexLearning.Threshold
