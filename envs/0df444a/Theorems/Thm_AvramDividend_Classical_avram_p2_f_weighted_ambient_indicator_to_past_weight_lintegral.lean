-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ambient_indicator_to_past_weight_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_ambient_indicator_to_past_weight_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:15:44.229198+00:00
-- url     : https://prove2.me/theorems/419a95ae-ab0d-41e2-bfdb-1bbeea21ae16
-- title:
--   True ambient-measure indicator-to-past-weight ENNReal compensation extension
-- statement:
--   For an ambient measure μ and an ambient-measurable ENNReal count N, with a separate smaller past sigma-algebra mPast, assume the exact event rectangle mean E[1_A N]=μ(A)r for all past events A. Then for any nonnegative mPast-measurable H, E[H N]=E[H]r. No finite expectation, independence, or specific ν-rate premise. The declaration pins μ and N's measurability to the ambient mΩ before introducing mPast, preventing Lean's local measurable-space inference from silently changing the integration σ-algebra. Proof by ENNReal measurable indicator/disjoint-sum/monotone-sup induction.
-- source:
--   Correct ambient-source contract for W7-06 event-to-adapted-weight and original P2-E predictable compensation, unlike the earlier preliminary helper 086b5c5f where Lean inferred the measure over the past sigma-algebra. Pin revision 0df444a3, use Mathlib Measurable.ennreal_induction, lintegral_indicator, const_mul, add_left, iSup, ENNReal.iSup_mul.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_ambient_indicator_to_past_weight_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℝ≥0∞) (hN : Measurable N)
    (mPast : MeasurableSpace Ω) (hm : mPast ≤ mΩ)
    (r : ℝ≥0∞)
    (hEvent : ∀ A : Set Ω, MeasurableSet[mPast] A →
      (∫⁻ ω in A, N ω ∂μ) = μ A * r)
    (H : Ω → ℝ≥0∞) (hH : Measurable[mPast] H) :
    (∫⁻ ω, H ω * N ω ∂μ) = (∫⁻ ω, H ω ∂μ) * r := by sorry
