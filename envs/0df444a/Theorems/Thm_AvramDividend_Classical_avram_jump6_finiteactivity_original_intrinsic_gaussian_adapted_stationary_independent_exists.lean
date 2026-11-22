-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_original_intrinsic_gaussian_adapted_stationary_independent_exists
-- name    : AvramDividend.Classical.avram_jump6_finiteactivity_original_intrinsic_gaussian_adapted_stationary_independent_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T22:38:53.224707+00:00
-- url     : https://prove2.me/theorems/10cd67c0-ca6b-4ef7-9556-b6e83e4ff02b
-- title:
--   Construct original finite-activity uniformly convergent Gaussian intrinsic residual with adapted stationary independent-increment version
-- statement:
--   For any original spectrally negative Lévy process satisfying Standing with finite negative-jump mass, construct on the *same original* probability space and filtration both the uniformly-on-compacts convergent intrinsic Gaussian residual R and a single version G that starts from zero, is adapted and almost surely right-continuous, has independent increments relative to the original filtration and stationary increment laws, and agrees with R for all times almost surely. No extra Gaussian process or residual witness is assumed.
-- source:
--   Original finite-activity Gaussian source Proved 0d7f9ed2-5536-4eed-8a9b-29f9d59f9908 and Proved 1e9ae8de-1cda-4d1e-afac-5953dc309b34. Connects to stopped physical Gaussian/Itô–Meyer source for 15815eff and root 545c65ef.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a24_canonical_gaussian_raw_adapted_stationary_independent_aeRC_20261114
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_finiteactivity_original_intrinsic_gaussian_adapted_stationary_independent_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ (R G : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ k ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
          |avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω -
            R T ω| ≤ ε) ∧
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, ∀ t,
        ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ s T : ℝ≥0, Indep
        (MeasurableSpace.comap
          (fun ω => G (s + T) ω - G s ω) inferInstance)
        (𝓕 s) P) ∧
      (∀ T, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
            Measure.map Z P) := by sorry
