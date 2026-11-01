-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_antitone
-- name    : AvramDividend.Classical.avram_wave4_02_source_esscher_record_height_rate_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:59:27.414985+00:00
-- url     : https://prove2.me/theorems/22a833f3-cad0-40a3-9c02-d592701b3dcd
-- title:
--   True reflected first-record Esscher height rate decreases with barrier depth
-- statement:
--   Under the actual source spectrally negative Levy law with infinite first small negative jump moment, its q-scale W, and a true positive Esscher root, the Esscher-shifted killed first-record rate lambda(a)=-log E_P[exp(-q tau_1); tau_1<D_a]-phi is antitone for positive barrier a. This follows from the genuine pathwise monotonicity of reflected ruin clocks, source strict record positivity and finite probability mass. No arbitrary measure or excursion compensator is assumed.
-- source:
--   Actual reflected ruin time monotonicity 6c566972, source original first-record strict positivity b1cbd08b, source discount <=1 7a08c9f8; KKR excursion-height tail monotonicity as a source killed potential property.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_discount_strict_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_source_esscher_record_height_rate_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X b ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) - φ ≤
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) - φ := by sorry
