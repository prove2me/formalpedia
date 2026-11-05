-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_finite_pair_mean_real_L1
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_finite_pair_mean_real_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:16:56.882196+00:00
-- url     : https://prove2.me/theorems/d4264254-647b-4c5f-b507-5d3f3bb0b11e
-- title:
--   Finite original chronological pair ENNReal mean yields physical real L1 and exact expectation
-- statement:
--   For the literal original Avram finite-band chronological pair cardinality K, if K is genuinely measurable on its original probability space and the ENNReal expected value of twice K is finite, then the real random variable 2*K is integrable with its real Bochner expectation exactly equal to the toReal of that original ENNReal expectation. This converts the source grid-limit expectation into the precise L1 and real expectation interface required by open chronological-pair theorem d938e9a5.
-- source:
--   Pinned Mathlib Real.enorm_eq_ofReal_abs and MeasureTheory.integral_eq_lintegral_of_nonneg_ae; source marked-jump finite set theorem; pair-limit bridge 92020479 (independent, proof currently pending).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_finite_pair_mean_real_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (F : Ω → Finset ℝ≥0)
    (hF : ∀ ω, F ω =
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω =
      ((F ω ×ˢ F ω).filter (fun p => p.1 < p.2)).card)
    (hKm : Measurable K)
    (hFinite : (∫⁻ ω, ((2 * K ω : ℕ) : ℝ≥0∞) ∂P) < ⊤) :
    Integrable (fun ω => (2 : ℝ) * (K ω : ℝ)) P ∧
    (∫ ω, (2 : ℝ) * (K ω : ℝ) ∂P) =
      (∫⁻ ω, ((2 * K ω : ℕ) : ℝ≥0∞) ∂P).toReal := by sorry
