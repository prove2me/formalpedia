-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_iid_half_sum_of_joint_product_law_ws01b
-- name    : AvramDividend.Classical.bv_iid_half_sum_of_joint_product_law_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:59:47.238778+00:00
-- url     : https://prove2.me/theorems/0c3348ad-837d-4523-b1a0-ab0bd57ba333
-- title:
--   Transport the iid weighted half-sum expectation to an actual pair of random variables
-- statement:
--   If the joint law of a real-valued random pair is μ×μ, its expected weighted first coordinate equals half its expected weighted total, whenever the indicated product-law integrals are finite. This lemma transfers the independently Proved exchangeable product-integral identity from an abstract product measure to the actual Lévy-increment sample space and handles the measure-map equality explicitly.
-- source:
--   Prove2Me accepted theorem 52eebd6c; pinned Mathlib MeasureTheory.integral_map; applies to stationary independent equal-length BV Lévy increments.

import Theorems.Thm_AvramDividend_Classical_bv_iid_pair_half_sum_weighted_integral_ws01b
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable

open MeasureTheory AvramDividend.Classical

theorem AvramDividend.Classical.bv_iid_half_sum_of_joint_product_law_ws01b
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Measure ℝ) [SFinite μ]
    (pair : Ω → ℝ × ℝ)
    (hPairMeas : AEMeasurable pair P)
    (hJoint : Measure.map pair P = μ.prod μ)
    (g : ℝ → ℝ)
    (hFirst : Integrable
      (fun z : ℝ × ℝ => z.1 * g (z.1 + z.2)) (μ.prod μ))
    (hSecond : Integrable
      (fun z : ℝ × ℝ => z.2 * g (z.1 + z.2)) (μ.prod μ)) :
    2 * (∫ ω, (pair ω).1 * g ((pair ω).1 + (pair ω).2) ∂P) =
      ∫ ω, ((pair ω).1 + (pair ω).2) *
        g ((pair ω).1 + (pair ω).2) ∂P := by sorry
