-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_unbounded_genuine_record_scale_sandwich
-- name    : AvramDividend.Classical.avram_wave3_01_unbounded_genuine_record_scale_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:25:33.876563+00:00
-- url     : https://prove2.me/theorems/f9f9bc34-1a49-425c-a348-1aa9d1b9cd75
-- title:
--   Standing-free original-Lévy reflected first-record q-scale ratio sandwich
-- statement:
--   For the actual spectrally negative Lévy process of unbounded variation, without Standing, the q-discounted probability of reaching an upward record height h before reflected ruin at depth a lies between W(a-h)/W(a) and W(a)/W(a+h). Both ordinary two-sided exit expectations are the canonically Proved Standing-free corrected q-scale ratios; the genuine strict prefix survival equivalence transfers their scale expectation to the reflected survival sandwich. This is the essential non-circular finite-difference input to pure-jump C1.
-- source:
--   Avram Palmowski Pistorius finite-difference sandwich; pinned Proved 8ce502f5, 7f14d8b9, caca9b2f, 6d3911f8. No Standing or C1 premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_raw_prefix_iff_strict_exit
import Theorems.Thm_AvramDividend_Classical_killedRecord_discount_scale_sandwich_of_raw_exit
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_unbounded_genuine_record_scale_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) (hha : h < a) :
    ENNReal.ofReal (W (a - h) / W a) ≤
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) ∧
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) ≤
    ENNReal.ofReal (W a / W (a + h)) := by sorry
