-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave4_02_source_esscher_record_height_rate_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:17:06.759958+00:00
-- url     : https://prove2.me/theorems/8b2f9051-ca6d-4469-8a68-5f888a9948cf
-- title:
--   True source Esscher killed-record height excess rate tends to zero at unbounded barriers
-- statement:
--   For the actual spectrally negative Levy source law with divergent first small-jump moment, q-scale W and positive Esscher root phi, the genuinely stopped first-record rate -log E_P[e^{-q tau_1}; tau_1<D_a]-phi decreases to zero as a→+∞. It is not an asserted Itô excursion intensity, but source-identified killed-record potential data needed for a proper height-tail representation.
-- source:
--   Actual first passage and reflected ruin clocks, Proved source height antitonicity and log-derivative, exact non-Standing Esscher C1, and established finite-limit flatness; KKR scale review Section 3 and Chan-Kyprianou-Savov smoothness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_positive_monotone_of_given_root
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_log_derivative_flatness
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_log_derivative
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_antitone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_02_source_esscher_record_height_rate_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    Tendsto (fun a : ℝ =>
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ) atTop (nhds (0 : ℝ)) := by sorry
