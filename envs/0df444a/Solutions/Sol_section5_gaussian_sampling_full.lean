-- Prove2me | solution 1 for section5_gaussian_sampling_full
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:24:14.718863+00:00
-- url     : https://prove2.me/submissions/acae9846-3713-46d3-8598-8741dca285cb

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Mathlib
import Theorems.Thm_section5_gaussian_amplitude_tail
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_multivariate_sampling_227
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

/-! The sampled Gaussian amplitude and its error before normalization. -/









theorem section5_gaussian_sampling_inside (n M : ℕ) (hM : 0 < M)
    (hsize : 128*(n:ℝ)^2 ≤ M) :
    Real.sqrt (∫ x : Fin n → ℝ,
      ‖section5_gaussian_amplitude n x-
        section5_gaussian_amplitude n (fun i => roundCoord M (x i))‖^2
      ∂(Measure.pi (fun _ : Fin n => section5_window_measure M))) ≤
        2*n*Real.sqrt (32/M) := by
  have hc : ∑ a : Fin n → Fin 1, ‖(1:ℂ)‖^2 = 1 := by simp
  have hh := section5_multivariate_sampling_227 n 1 M hM (by norm_num; linarith)
    (fun _ => (1:ℂ)) hc
  have hz (a : Fin n → Fin 1) (x : Fin n → ℝ) :
      (∏ i, section5_complex_wave 1 (a i) (x i)) = section5_gaussian_amplitude n x :=
    section5_tensor_wave_zero n a x
  simp_rw [hz] at hh
  norm_num only [Nat.cast_one] at hh
  simpa only [one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    one_pow,one_nsmul] using hh

theorem section5_integral_indicator_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Set α) (hs : MeasurableSet s) (f : α → ℂ) :
    (∫ x, ‖s.indicator f x‖^2 ∂μ) = ∫ x in s, ‖f x‖^2 ∂μ := by
  have heq : (fun x => ‖s.indicator f x‖^2) = s.indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [heq,integral_indicator hs]



end
section
set_option autoImplicit false

open MeasureTheory

/-! Product-space estimates for the multivariate Hermite sampling argument.
All product integrals are justified before Fubini is used.
-/



theorem section5_l2_energy_triangle {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ x, ‖f x+g x‖^2 ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖^2 ∂μ)+Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  have ha : (hf.add hg).toLp (f+g) = hf.toLp f+hg.toLp g := by
    apply Lp.ext
    filter_upwards [(hf.add hg).coeFn_toLp,hf.coeFn_toLp,hg.coeFn_toLp,
      Lp.coeFn_add (hf.toLp f) (hg.toLp g)] with x hsum hfx hgx hadd
    simp only [hsum,hadd,Pi.add_apply,hfx,hgx]
  rw [← section5_l2_norm_sq f hf,← section5_l2_norm_sq g hg]
  change Real.sqrt (∫ x, ‖(f+g) x‖^2 ∂μ) ≤ _
  rw [← section5_l2_norm_sq (f+g) (hf.add hg),ha]
  simpa only [Real.sqrt_sq (norm_nonneg _)] using norm_add_le (hf.toLp f) (hg.toLp g)













































end
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example Aux_w_53_hermite
theorem solution (n M : ℕ) (hM : 0 < M)
    (hsize : 128*(n:ℝ)^2 ≤ M) :
    Real.sqrt (∫ x : Fin n → ℝ,
      ‖section5_sampled_gaussian_amplitude n M x-section5_gaussian_amplitude n x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) ≤
        2*n*Real.sqrt (32/M)+Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
  let s := section5_grid_box n M
  let A := fun x : Fin n → ℝ => section5_gaussian_amplitude n (fun i => roundCoord M (x i))
  let B := section5_gaussian_amplitude n
  let μ := Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
  have hB : MemLp B 2 μ := section5_gaussian_amplitude_memLp n
  have hA : MemLp (s.indicator A) 2 μ := section5_sampled_gaussian_memLp n M hM
  have hs := section5_grid_box_measurable n M
  have hB' := hB.indicator hs
  have hT := hB.indicator hs.compl
  have hdiff : s.indicator (A-B) = s.indicator A-s.indicator B := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hinside : MemLp (s.indicator (A-B)) 2 μ := by
    rw [hdiff]
    exact hA.sub hB'
  have hsplit : (fun x => section5_sampled_gaussian_amplitude n M x-B x) =
      fun x => s.indicator (A-B) x+(-(sᶜ.indicator B)) x := by
    funext x
    by_cases hx : x ∈ s <;> simp [section5_sampled_gaussian_amplitude,s,A,B,hx]
  have h := section5_l2_energy_triangle (s.indicator (A-B)) (-(sᶜ.indicator B)) hinside hT.neg
  have hi : Real.sqrt (∫ x, ‖s.indicator (A-B) x‖^2 ∂μ) ≤ 2*n*Real.sqrt (32/M) := by
    rw [section5_integral_indicator_norm_sq s hs,← section5_window_pi]
    have hi' := section5_gaussian_sampling_inside n M hM hsize
    simpa only [Pi.sub_apply,norm_sub_rev] using hi'
  have ht : Real.sqrt (∫ x, ‖(-(sᶜ.indicator B)) x‖^2 ∂μ) ≤
      Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
    simp only [Pi.neg_apply,norm_neg]
    rw [section5_integral_indicator_norm_sq sᶜ hs.compl]
    exact section5_gaussian_amplitude_tail n M hM
  have heq (x : Fin n → ℝ) : section5_sampled_gaussian_amplitude n M x-B x =
      s.indicator (A-B) x+(-(sᶜ.indicator B)) x := congrFun hsplit x
  have henergy : (fun x => ‖section5_sampled_gaussian_amplitude n M x-B x‖^2) =
      fun x => ‖s.indicator (A-B) x+(-(sᶜ.indicator B)) x‖^2 := by
    funext x
    exact congrArg (fun z : ℂ => ‖z‖^2) (heq x)
  exact (congrArg (fun F : (Fin n → ℝ) → ℝ => Real.sqrt (∫ x, F x ∂μ)) henergy).le.trans
    (h.trans (add_le_add hi ht))
