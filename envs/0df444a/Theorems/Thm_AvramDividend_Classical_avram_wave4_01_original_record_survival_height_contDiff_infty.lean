-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_height_contDiff_infty
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_survival_height_contDiff_infty
-- status  : Open
-- author  : @WillR
-- created : 2026-10-31T19:20:58.017983+00:00
-- url     : https://prove2.me/theorems/b6247e7a-8652-4e41-b7a1-d3be62070834
-- title:
--   Original first-record discount is C-infinity in positive record height under pure infinite small-jump variation, without Standing
-- statement:
--   For the original spectrally negative Lévy process, without Standing, with positive discount q and divergent first absolute small-negative-jump moment, the genuine killed first strict-upward-record survival discount h↦E[e^{-q T_h};T_h<D_a] is smooth of every finite order on positive heights, at every positive drawdown depth a. This uses the already proved genuine source exact spatial exponential representation and real exponential smoothness, not a tilted or excursion surrogate.
-- source:
--   Proved avram_wave4_01_original_record_discount_exp_log_scale_deriv and pinned Mathlib Real.contDiff_exp, ContDiff.comp and ContDiffOn.congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_survival_height_contDiff_infty
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (a : ℝ) (ha : 0 < a) :
    ContDiffOn ℝ ⊤ (fun h : ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) (Ioi 0) := by sorry
