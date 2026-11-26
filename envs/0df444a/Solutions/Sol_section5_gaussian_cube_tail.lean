-- Prove2me | solution 1 for section5_gaussian_cube_tail
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:02.284156+00:00
-- url     : https://prove2.me/submissions/7fcaa997-2eb9-4dcb-89ac-6c3ed7354d6e

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

/-! Gaussian density and tail estimates for Appendix D, Eq. 230. -/

theorem section5_gaussian_upper_tail (L : ℝ) (hL : 0 ≤ L) :
    (gaussianReal 0 1).real {x : ℝ | L ≤ x} ≤ Real.exp (-L^2/2) := by
  have h := measure_ge_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 1) L hL
    (integrable_exp_mul_gaussianReal L)
  rw [mgf_id_gaussianReal] at h
  simp only [zero_mul,NNReal.coe_one,one_mul,zero_add,← Real.exp_add] at h
  convert h using 1 <;> congr 1 <;> ring

theorem section5_gaussian_lower_tail (L : ℝ) (hL : 0 ≤ L) :
    (gaussianReal 0 1).real {x : ℝ | x ≤ -L} ≤ Real.exp (-L^2/2) := by
  have h := measure_le_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 1) (-L) (neg_nonpos.mpr hL)
    (integrable_exp_mul_gaussianReal (-L))
  rw [mgf_id_gaussianReal] at h
  simp only [zero_mul,NNReal.coe_one,one_mul,zero_add,← Real.exp_add] at h
  convert h using 1 <;> congr 1 <;> ring

theorem section5_gaussian_two_sided_tail (L : ℝ) (hL : 0 ≤ L) :
    (gaussianReal 0 1).real {x : ℝ | L ≤ |x|} ≤ 2*Real.exp (-L^2/2) := by
  have heq : {x : ℝ | L ≤ |x|} = {x : ℝ | L ≤ x} ∪ {x : ℝ | x ≤ -L} := by
    ext x
    change L ≤ |x| ↔ L ≤ x ∨ x ≤ -L
    rw [le_abs]
    constructor <;> intro h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [heq]
  exact (measureReal_union_le (μ := gaussianReal 0 1) _ _).trans
    ((add_le_add (section5_gaussian_upper_tail L hL) (section5_gaussian_lower_tail L hL)).trans_eq (by ring))





































end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example
theorem solution (n : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {x : Fin n → ℝ | ∃ i, L ≤ |x i|} ≤ 2*n*Real.exp (-L^2/2) := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  have heq : {x : Fin n → ℝ | ∃ i, L ≤ |x i|} = ⋃ i : Fin n, {x | L ≤ |x i|} := by
    ext x; simp
  rw [heq]
  calc
    _ ≤ ∑ i : Fin n, μ.real {x | L ≤ |x i|} := measureReal_iUnion_fintype_le (μ := μ) _
    _ ≤ ∑ _i : Fin n, 2*Real.exp (-L^2/2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hmp := measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i
      have hh : μ.real {x : Fin n → ℝ | L ≤ |x i|} =
          (gaussianReal 0 1).real {x : ℝ | L ≤ |x|} := by
        rw [← hmp.map_eq]
        exact (map_measureReal_apply (measurable_pi_apply i)
          (measurableSet_le measurable_const measurable_abs)).symm
      rw [hh]
      exact section5_gaussian_two_sided_tail L hL
    _ = _ := by simp; ring
