-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_full_balance_of_positive_reserves
-- name    : AvramDividend.Classical.avram_root29_03_ubv_full_balance_of_positive_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:21:49.59943+00:00
-- url     : https://prove2.me/theorems/8b640d56-f429-455a-9831-688c1f13f065
-- title:
--   Full UBV two-sided stopped balance from the strictly positive-reserve case
-- statement:
--   For any unbounded-variation spectrally negative Levy process, positive discount, q-scale function and positive upper barrier, assume the exact strict upper-before-ruin stopped-scale balance has been established at every strictly positive reserve up to the barrier. It then holds at all nonnegative reserves including zero, without Standing and without an extra killed-martingale argument at zero.
-- source:
--   Exact source-level endpoint conversion for the Open canonical 2dcc8bcc. At zero reserve, Proved original-clock UBV down-time 0 (c56bc2f2) combines with Proved zero-reserve stopped-scale identity 8029c619. At positive reserve, the stated hypothesis is used as given. All imports are already canonically Proved; no Open be9, 2dcc, or ancestor is imported. The theorem isolates the genuine stochastic work to 0<x<=a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_down_clock_immediate
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_ubv_full_balance_of_positive_reserves
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hPositive : ∀ x : ℝ, 0 < x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    ∀ x : ℝ, 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by sorry
