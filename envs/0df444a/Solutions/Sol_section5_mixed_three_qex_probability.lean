-- Prove2me | solution 1 for section5_mixed_three_qex_probability
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:10.470831+00:00
-- url     : https://prove2.me/submissions/651f8470-5034-4a14-9f94-d7e411d0ffab

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5MixedQEXMeasurement
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_basis_permutation_conjugation
import Theorems.Thm_section5_three_qex_weighted_measurement
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Exact measurement laws for reversible classical post-processing. These hold
for arbitrary input matrices, so coherences between measurement transcripts do
not have to be discarded by an unproved intermediate-measurement assumption. -/



theorem section5_basis_permutation_probMixed {ι : Type} [Fintype ι] [DecidableEq ι]
    (U ρ : Matrix ι ι ℂ) (f : Equiv.Perm ι)
    (hact : ∀ x, act U (ket x)=ket (f x)) (P : ι → Prop) [DecidablePred P] :
    probMixed U ρ P=∑ x : ι, if P (f x) then (ρ x x).re else 0 := by
  unfold probMixed
  rw [Finset.sum_filter,← Equiv.sum_comp f]
  simp only [section5_basis_permutation_conjugation U ρ f hact]







end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement QuantumLTF.Example
open scoped ComplexConjugate

/-! Three independent QEX states tensored with an arbitrary mixed data register.
Classical post-processing depends only on the diagonal data probabilities; the
proof retains all input coherences and does not assume an intermediate measurement. -/



theorem section5_mixed_qex_diagonal {ι α : Type*} {n q : ℕ}
    (E : ι ≃ α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)))
    (σ : Matrix α α ℂ) (w : EuclideanSpace ℝ (Fin n)) (y : ι) :
    (section5_mixed_qex_density E σ w y y).re=
      (σ (E y).1 (E y).1).re*prob (section5_three_qex_state (q:=q) w) (E y).2 := by
  unfold section5_mixed_qex_density
  rw [mul_assoc,Complex.mul_conj]
  simp [Complex.mul_re,Complex.normSq_eq_norm_sq,prob,ket,EuclideanSpace.inner_single_left]
  simp only [← Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement QuantumLTF.Example
open scoped ComplexConjugate
theorem solution {ι α : Type} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] {n q : ℕ}
    (E : ι ≃ α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)))
    (σ : Matrix α α ℂ) (w : EuclideanSpace ℝ (Fin n))
    (U : Matrix ι ι ℂ) (F : Equiv.Perm ι) (hact : ∀ z, act U (ket z)=ket (F z))
    (P : ι → Prop) [DecidablePred P] :
    probMixed U (section5_mixed_qex_density E σ w) P=
      ∑ d : α, ∑ x : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
        if P (F (E.symm (d,section5_labelled_three_qex_outcome w x))) then
          (σ d d).re*section5_three_qex_weight n q x else 0 := by
  rw [section5_basis_permutation_probMixed U _ F hact P]
  simp only [section5_mixed_qex_diagonal]
  rw [← Equiv.sum_comp E.symm]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  let G : α → (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)) → ℝ :=
    fun d z => if P (F (E.symm (d,z))) then 1 else 0
  calc
    _ = ∑ d : α, (σ d d).re*
        (∑ z, prob (section5_three_qex_state (q:=q) w) z*G d z) := by
      simp only [Finset.mul_sum,G,mul_ite,mul_one,mul_zero]
    _ = ∑ d : α, (σ d d).re*
        (∑ x, section5_three_qex_weight n q x*G d (section5_labelled_three_qex_outcome w x)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [section5_three_qex_weighted_measurement]
    _ = _ := by simp only [Finset.mul_sum,G,mul_ite,mul_one,mul_zero]
