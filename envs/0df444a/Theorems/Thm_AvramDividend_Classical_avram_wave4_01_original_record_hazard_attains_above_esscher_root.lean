-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_attains_above_esscher_root
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_hazard_attains_above_esscher_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:45:16.184372+00:00
-- url     : https://prove2.me/theorems/f47cd658-af30-4bcb-952d-6aae612ccd14
-- title:
--   Every reflected first-record hazard level above the Esscher root is attained at a finite drawdown depth
-- statement:
--   For the actual strict first upward record T_1 and actual reflected drawdown ruin D_a of a spectrally negative Levy process with divergent negative small-jump absolute first moment, positive discount q, and the positive Esscher root phi, every target lambda>phi equals the genuine killed first-record logarithmic hazard -log E[exp(-q T_1);T_1<D_a] at some finite a>0. This follows from proved source hazard continuity, its divergence as a decreases to zero, and its convergence to phi as a tends to infinity. Neither Standing nor a surrogate excursion axiom is assumed.
-- source:
--   Direct original-process descendant of source hazard continuity ec9e934a-2ad2-4a0d-8d6e-9dd9654ab798, zero-depth blow-up 800cd189-f02c-439e-8919-17259775ab86, infinity limit d455bcb7-c70c-47a4-b83d-cc0d689003b6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_tendsto_esscher_root
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_hazard_attains_above_esscher_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (targetRate : ℝ) (htargetRate : φ < targetRate) :
    ∃ a : ℝ, 0 < a ∧
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) = targetRate := by sorry
