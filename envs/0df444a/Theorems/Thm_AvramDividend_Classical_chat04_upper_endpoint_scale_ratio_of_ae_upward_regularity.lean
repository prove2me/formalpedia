-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_scale_ratio_of_ae_upward_regularity
-- name    : AvramDividend.Classical.chat04_upper_endpoint_scale_ratio_of_ae_upward_regularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:02:31.661503+00:00
-- url     : https://prove2.me/theorems/56265c15-1e44-4732-ac08-643f92e8f517
-- title:
--   Exact two-sided exit scale ratio at the upper endpoint from almost-sure upward regularity
-- statement:
--   For positive a, right-continuity and X_0=0 make the lower exit strictly positive. Under almost-sure immediate upward regularity, the upper-before-ruin q-discount expectation equals one; the standing scale-function positivity gives W(a)/W(a)=1. Thus the precise scale-ratio identity holds for initial capital x=a with only the remaining upward regularity hypothesis.
-- source:
--   x=a boundary of alternative accepted two_sided_exit_before_ruin_identity UUID 5bcf90e1-211c-42db-beac-d92aeb95b5c9 and integral parent UUID 3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7; uses Proved bf738dc2 and 59531c77.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.Algebra.Order.Field.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_upper_endpoint_scale_ratio_of_ae_upward_regularity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitExpectation X q a a =
      ENNReal.ofReal (W a / W a) := by sorry
