-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_exit_ratio_of_near_zero
-- name    : AvramDividend.Classical.chat04_unbounded_zero_start_exit_ratio_of_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:30:56.873463+00:00
-- url     : https://prove2.me/theorems/23672221-e26a-40e7-9c55-419a0f6eb1cc
-- title:
--   Zero-reserve strict two-sided q-discounted exit ratio in the unbounded-variation case
-- statement:
--   Under unbounded variation and almost-sure negative path values arbitrarily near zero time, the expected discount for exiting a before ruin starting with capital zero is zero, and the q-scale ratio W(0)/W(a) is zero because the scale function vanishes at the origin. Thus the canonical two-sided exit-ratio identity holds exactly at initial reserve zero for any positive a without invoking optional stopping for positive reserves.
-- source:
--   Composes Proved chat04_scale_zero_origin_of_unbounded_variation with new chat04_zero_start_two_sided_exit_expectation_of_near_zero (6af17860-9f60-41a5-b3db-696c4838f482). It is the exact x=0 branch of alternative Open two_sided_exit_before_ruin_identity (5bcf90e1-211c-42db-beac-d92aeb95b5c9), and parent 3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_zero_start_two_sided_exit_expectation_of_near_zero
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_zero_start_exit_ratio_of_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hnear : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    twoSidedExitExpectation X q a 0 =
      ENNReal.ofReal (W 0 / W a) := by sorry
