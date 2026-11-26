-- Prove2me | solution 1 for section5_wave_sum_product_integral
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:51.08829+00:00
-- url     : https://prove2.me/submissions/57cd8cc8-07b9-44dc-a9a3-dc883fd3d53b

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
import Theorems.Thm_Aux_w_53_hermite_h1D_orthonormal_aux
section
set_option autoImplicit false

open MeasureTheory Aux_w_53_hermite

/-! The normalized Hermite functions and the derivative estimate required by Appendix D. -/









theorem section5_hermite_wave_orthonormal (j k : ℕ) :
    (∫ x : ℝ, section5_hermite_wave j x * section5_hermite_wave k x) =
      if j=k then 1 else 0 := by
  simp_rw [section5_hermite_wave_product]
  exact h1D_orthonormal_aux j k



































































end
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℕ) (v : κ → ℕ) :
    (∫ x : ℝ, (∑ i, a i*section5_hermite_wave (u i) x)*
      (∑ j, b j*section5_hermite_wave (v j) x)) =
      ∑ i, ∑ j, (a i*b j)*(if u i=v j then 1 else 0) := by
  have heq : (fun x => (∑ i, a i*section5_hermite_wave (u i) x)*
      (∑ j, b j*section5_hermite_wave (v j) x)) =
      fun x => ∑ i, ∑ j, (a i*b j)*
        (section5_hermite_wave (u i) x*section5_hermite_wave (v j) x) := by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (section5_hermite_wave_integrable_product _ _).const_mul _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ =>
    (section5_hermite_wave_integrable_product _ _).const_mul _)]
  simp_rw [integral_const_mul, section5_hermite_wave_orthonormal]
