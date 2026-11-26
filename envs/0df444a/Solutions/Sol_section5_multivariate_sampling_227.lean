-- Prove2me | solution 1 for section5_multivariate_sampling_227
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:20:32.796459+00:00
-- url     : https://prove2.me/submissions/69360523-fb0f-423d-aa24-909393438164

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_complex_series_integral_sq
import Theorems.Thm_section5_hermite_roundCoord_error
import Theorems.Thm_section5_hybrid_linear_bound
import Theorems.Thm_section5_tensor_synthesis_error
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

/-! The multivariate Hermite sampling estimate of Appendix D, Eq. 227. -/











theorem section5_wave_window_synthesis_bound (D M : ℕ) :
    section5_SynthesisBound (section5_window_measure M) (section5_complex_wave D) 1 := by
  intro c
  have hi := (section5_memLp_synthesis (section5_complex_wave D)
    (section5_complex_wave_memLp D) c).norm.integrable_sq
  calc
    _ ≤ ∫ x : ℝ, ‖section5_complex_hermite_series c x‖^2 :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    _ = _ := by rw [section5_complex_series_integral_sq]; simp





theorem section5_wave_sampling_synthesis_bound (D M : ℕ) (hM : 0 < M) :
    section5_SynthesisBound (section5_window_measure M)
      (fun k x => section5_complex_wave D k x-section5_complex_wave D k (roundCoord M x))
      (Real.sqrt (16*(D+1)/M)) := by
  intro c
  have h := section5_hermite_roundCoord_error c M hM
  have hL : -gridRadius M ≤ gridRadius M := by
    have : 0 ≤ gridRadius M := by unfold gridRadius gridSpacing; positivity
    linarith
  rw [intervalIntegral.integral_of_le hL] at h
  rw [Real.sq_sqrt (by positivity)]
  simpa only [section5_window_measure,section5_complex_wave,section5_complex_hermite_series,mul_sub,
    Finset.sum_sub_distrib] using h

theorem section5_sampling_grid_small (n D M : ℕ) (hM : 0 < M)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ M) :
    (n:ℝ)*Real.sqrt (16*(D+1)/M) ≤ 1/2 := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hsq : ((n:ℝ)*Real.sqrt (16*(D+1)/M))^2 ≤ (1/2:ℝ)^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity),← mul_div_assoc]
    apply (div_le_iff₀ hM').mpr
    nlinarith
  have hn : 0 ≤ (n:ℝ)*Real.sqrt (16*(D+1)/M) := by positivity
  nlinarith



end
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

theorem solution (n D M : ℕ) (hM : 0 < M)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ M) (c : (Fin n → Fin D) → ℂ)
    (hc : ∑ a, ‖c a‖^2 = 1) :
    Real.sqrt (∫ x : Fin n → ℝ,
      ‖(∑ a, c a*∏ i, section5_complex_wave D (a i) (x i))-
        (∑ a, c a*∏ i, section5_complex_wave D (a i) (roundCoord M (x i)))‖^2
      ∂(Measure.pi (fun _ : Fin n => section5_window_measure M))) ≤
        2*n*Real.sqrt (16*(D+1)/M) := by
  let δ := Real.sqrt (16*(D+1)/M)
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have hf (k : Fin D) : MemLp (section5_complex_wave D k) 2 (section5_window_measure M) :=
    (section5_complex_wave_memLp D k).restrict _
  have hg := section5_sampled_wave_memLp D M hM
  have hh := section5_tensor_synthesis_error (section5_window_measure M)
    (section5_complex_wave D) (fun k x => section5_complex_wave D k (roundCoord M x)) hf hg
    δ hδ (section5_wave_window_synthesis_bound D M) (section5_wave_sampling_synthesis_bound D M hM) n c
  simp only [hc,mul_one,mul_sub,Finset.sum_sub_distrib,section5_tensor_family] at hh
  have hpow : 0 ≤ (1+δ)^n-1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hroot := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq hpow] at hroot
  exact hroot.trans (section5_hybrid_linear_bound n δ hδ (section5_sampling_grid_small n D M hM hsize))
