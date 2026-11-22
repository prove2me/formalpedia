-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_true_ruinclipped_terminal_original_continuous_G_and_centered_Jsmall
-- name    : AvramDividend.Classical.avram_jump6_finiteactivity_true_ruinclipped_terminal_original_continuous_G_and_centered_Jsmall
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T22:47:08.794843+00:00
-- url     : https://prove2.me/theorems/79a192d2-2e1b-4360-b00c-f802745bebdd
-- title:
--   Original finite-activity true ruin-clipped reserve equals continuous Gaussian plus stopped centred small jumps and full negative marks
-- statement:
--   For the exact original finite-activity spectrally negative Lévy process with Standing, arbitrary original dividend strategy and canonical physical ruin-truncated τ, construct a single adapted continuous centred Gaussian martingale G and an integrable compensated negative small-mark field Jsmall with zero initial-conditional expectation at τ. Prove the physical post-right-dividend true stopped terminal W equals x+τ·c+Gτ+Jsmallτ+the actual original large-jump sum minus the dividend rightLimit at initial/strict pre-ruin or D at ruin contact, all on original Ω. The mathematical statement makes no artificial Brownian or jump witness assumption.
-- source:
--   Proved original-source 0d7f9ed2,33051068,1c983d3d,61f39bfe and 85c316b5; next mathematical bridge towards finiteactivity stopped Ito-Meyer expected reward 15815eff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_finiteactivity_true_ruinclipped_terminal_original_continuous_G_and_centered_Jsmall
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∃ (G Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (G t) ω = G s ω) ∧
      (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun η => Jsmall (τ η) η) ω = 0) ∧
      (∀ᵐ ω ∂P, W ω =
        x + (τ ω : ℝ) * X.c + G (τ ω) ω + Jsmall (τ ω) ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
        (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
         then rightLimit D (τ ω) ω else D (τ ω) ω)) := by sorry
