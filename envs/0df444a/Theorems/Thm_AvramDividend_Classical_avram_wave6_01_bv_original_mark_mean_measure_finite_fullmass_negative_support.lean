-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_mark_mean_measure_finite_fullmass_negative_support
-- name    : AvramDividend.Classical.avram_wave6_01_bv_original_mark_mean_measure_finite_fullmass_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:04:51.592204+00:00
-- url     : https://prove2.me/theorems/ab18c0b6-5b9e-4b4e-80bf-1a68c45b737e
-- title:
--   The finite-BV actual original jump-mark mean is finite, negatively supported, and has exact total Lévy mass
-- statement:
--   For the same original bounded-variation finite-total-jump-intensity spectrally negative Lévy process X, the actual original first-moment mark counting measure ρ_T(B)=E_P N_X((0,T]×B) exists as a finite measure on ℝ. Its full mass is exactly T·X.ν((−∞,0)), and it vanishes on [0,∞); no arbitrary-mark ν(B) identity is assumed. This packages the already Proved original kernel, original full-count first moment, and pointwise original negative-jump support into the finite measure interface needed for source mark-Laplace uniqueness.
-- source:
--   Canonically Proved source expected mark measure 7ffab5e4, source original total first-moment rate 4d7761f5, original intrinsic negative support 12e84fff; finite ENNReal multiplication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_jump_mark_measure_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_original_mark_mean_measure_finite_fullmass_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ ρ : Measure ℝ,
      ρ (Set.univ : Set ℝ) =
        (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
      ρ (Ici (0 : ℝ)) = 0 ∧
      ρ (Set.univ : Set ℝ) < ⊤ ∧
      ∀ B : Set ℝ, MeasurableSet B →
        ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) := by sorry
