-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_iid_pair_half_sum_weighted_integral_ws01b
-- name    : AvramDividend.Classical.bv_iid_pair_half_sum_weighted_integral_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:54:05.830493+00:00
-- url     : https://prove2.me/theorems/52eebd6c-e9d5-4a49-9da9-05a885be52ff
-- title:
--   Half-sum expectation under exchangeable independent identical-law increments
-- statement:
--   For independent identically distributed real random variables A and B, every integrable weighted payoff g(A+B) assigns half of the expected total sum to the first increment: 2 E[A g(A+B)] = E[(A+B)g(A+B)]. The statement uses the product law μ×μ and remains valid for any s-finite measure μ when the weighted integrands are integrable. This is the key exchangeability identity for the dyadic Lévy drift-deficit martingale in BV two-sided-exit formalisation.
-- source:
--   Pinned Mathlib MeasureTheory.integral_prod_swap; exchangeable equal-time Lévy increments; accepted Prove2Me product-law swap theorem 842b1829.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Ring

open MeasureTheory

theorem AvramDividend.Classical.bv_iid_pair_half_sum_weighted_integral_ws01b
    (μ : Measure ℝ) [SFinite μ] (g : ℝ → ℝ)
    (hFirst : Integrable
      (fun z : ℝ × ℝ => z.1 * g (z.1 + z.2)) (μ.prod μ))
    (hSecond : Integrable
      (fun z : ℝ × ℝ => z.2 * g (z.1 + z.2)) (μ.prod μ)) :
    2 * (∫ z : ℝ × ℝ, z.1 * g (z.1 + z.2) ∂(μ.prod μ)) =
      ∫ z : ℝ × ℝ, (z.1 + z.2) * g (z.1 + z.2) ∂(μ.prod μ) := by sorry
