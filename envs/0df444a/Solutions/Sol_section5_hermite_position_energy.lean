-- Prove2me | solution 1 for section5_hermite_position_energy
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:50.48052+00:00
-- url     : https://prove2.me/submissions/f2c6e246-5dd7-4fe9-9f1f-6468f52b6ed0

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Mathlib
import Theorems.Thm_Aux_w_53_hermite_x_mul_h1D_eq
import Theorems.Thm_section5_hermite_lower_integral_sq
import Theorems.Thm_section5_wave_sum_integrable_product
import Theorems.Thm_section5_wave_sum_product_integral
section
set_option autoImplicit false

open MeasureTheory Aux_w_53_hermite

/-! The normalized Hermite functions and the derivative estimate required by Appendix D. -/



















theorem section5_wave_sum_norm_sq {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (u : ι → ℕ) (hu : Function.Injective u) :
    (∫ x : ℝ, (∑ i, a i*section5_hermite_wave (u i) x)^2) = ∑ i, (a i)^2 := by
  classical
  simp_rw [pow_two]
  rw [section5_wave_sum_product_integral]
  simp [hu.eq_iff]















theorem section5_hermite_upper_integral_sq {D : ℕ} (c : Fin D → ℝ) :
    (∫ x : ℝ, (section5_hermite_upper c x)^2) = ∑ k, (c k)^2*((k:ℕ)+1) := by
  classical
  unfold section5_hermite_upper
  rw [section5_wave_sum_norm_sq _ _ (fun i j h => Fin.ext (Nat.add_right_cancel h))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow, Real.sq_sqrt (by positivity)]











theorem section5_hermite_wave_position (k : ℕ) (x : ℝ) :
    x*section5_hermite_wave k x =
      Real.sqrt k*section5_hermite_wave (k-1) x +
        Real.sqrt (k+1)*section5_hermite_wave (k+1) x := by
  have hx := x_mul_h1D_eq k x
  unfold section5_hermite_wave
  calc
    _ = Real.sqrt (phi x)*(x*h1D k x) := by ring
    _ = _ := by rw [hx]; by_cases hk : k=0 <;> simp [hk] <;> ring

theorem section5_hermite_series_position {D : ℕ} (c : Fin D → ℝ) (x : ℝ) :
    x*section5_hermite_series c x = section5_hermite_lower c x+section5_hermite_upper c x := by
  unfold section5_hermite_series section5_hermite_lower section5_hermite_upper
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = c k*(x*section5_hermite_wave k x) := by ring
    _ = _ := by rw [section5_hermite_wave_position]; ring

theorem section5_hermite_position_integrable_sq {D : ℕ} (c : Fin D → ℝ) :
    Integrable (fun x => x^2*(section5_hermite_series c x)^2) := by
  have hlo : Integrable (fun x => (section5_hermite_lower c x)^2) := by
    simpa only [section5_hermite_lower, pow_two] using
      section5_wave_sum_integrable_product (fun k => c k*Real.sqrt k)
        (fun k => c k*Real.sqrt k) (fun k : Fin D => (k:ℕ)-1) (fun k => (k:ℕ)-1)
  have hhi : Integrable (fun x => (section5_hermite_upper c x)^2) := by
    simpa only [section5_hermite_upper, pow_two] using
      section5_wave_sum_integrable_product (fun k => c k*Real.sqrt ((k:ℕ)+1))
        (fun k => c k*Real.sqrt ((k:ℕ)+1)) (fun k : Fin D => (k:ℕ)+1) (fun k => (k:ℕ)+1)
  have hcross : Integrable (fun x => section5_hermite_lower c x*section5_hermite_upper c x) :=
    section5_wave_sum_integrable_product _ _ _ _
  have heq : (fun x => x^2*(section5_hermite_series c x)^2) = fun x =>
      (section5_hermite_lower c x)^2 +
        2*(section5_hermite_lower c x*section5_hermite_upper c x) +
          (section5_hermite_upper c x)^2 := by
    funext x
    rw [← mul_pow, section5_hermite_series_position]
    ring
  rw [heq]
  exact (hlo.add (hcross.const_mul 2)).add hhi

























end
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite
theorem solution {D : ℕ} (c : Fin D → ℝ) :
    (∫ x : ℝ, x^2*(section5_hermite_series c x)^2) ≤ 4*(D+1)*∑ k, (c k)^2 := by
  have hlo : Integrable (fun x => (section5_hermite_lower c x)^2) := by
    simpa only [section5_hermite_lower, pow_two] using
      section5_wave_sum_integrable_product (fun k => c k*Real.sqrt k)
        (fun k => c k*Real.sqrt k) (fun k : Fin D => (k:ℕ)-1) (fun k => (k:ℕ)-1)
  have hhi : Integrable (fun x => (section5_hermite_upper c x)^2) := by
    simpa only [section5_hermite_upper, pow_two] using
      section5_wave_sum_integrable_product (fun k => c k*Real.sqrt ((k:ℕ)+1))
        (fun k => c k*Real.sqrt ((k:ℕ)+1)) (fun k : Fin D => (k:ℕ)+1) (fun k => (k:ℕ)+1)
  calc
    _ ≤ ∫ x : ℝ, 2*((section5_hermite_lower c x)^2+(section5_hermite_upper c x)^2) := by
      apply integral_mono (section5_hermite_position_integrable_sq c) ((hlo.add hhi).const_mul 2)
      intro x
      change x^2*(section5_hermite_series c x)^2 ≤
        2*((section5_hermite_lower c x)^2+(section5_hermite_upper c x)^2)
      rw [← mul_pow, section5_hermite_series_position]
      nlinarith [sq_nonneg (section5_hermite_lower c x-section5_hermite_upper c x)]
    _ = 2*((∑ k, (c k)^2*(k:ℕ))+(∑ k, (c k)^2*((k:ℕ)+1))) := by
      rw [integral_const_mul, integral_add hlo hhi,
        section5_hermite_lower_integral_sq, section5_hermite_upper_integral_sq]
    _ ≤ _ := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hk' : ((k:ℕ):ℝ) < D := by exact_mod_cast k.isLt
      nlinarith [sq_nonneg (c k)]
