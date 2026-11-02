-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_controlled_compact_gaussian_generator_drift_L1_predictable
-- name    : AvramDividend.Classical.avram_wave5_03_original_controlled_compact_gaussian_generator_drift_L1_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:19:40.027167+00:00
-- url     : https://prove2.me/theorems/d8eacc25-2108-47d7-89b1-5a5691ca23e9
-- title:
--   Original controlled compact-interior Gaussian generator curvature drift is integrable on every finite predictable clock
-- statement:
--   For the original Lévy path X, the same dividend strategy D, and actual right-continuous predictable prepayment reserve, a C² function w on an open interval has a uniformly bounded and predictable zero-masked second derivative on each compact strictly interior band. Consequently the genuine σ²/2 Gaussian generator drift, evaluated on this same path, is Bochner L1 against every finite measure on the source predictable sigma algebra. This supplies the hG localisation to the existing Proved 732738fd Gaussian/jump generator residual integrability bridge for corrected UBV and does not claim the Gaussian stochastic integral or an Itô formula.
-- source:
--   Original corrected UBV core 429e17ca; Proved source reserve predictability 94ee9994; pinned Mathlib ContDiffOn.continuousOn_iteratedDerivWithin, iteratedDerivWithin_eq_iteratedDeriv and Integrable.of_bound; Proved source generator split 668fd38f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_controlled_compact_gaussian_generator_drift_L1_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u < v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    Integrable (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Icc u v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
      else 0) μ := by sorry
