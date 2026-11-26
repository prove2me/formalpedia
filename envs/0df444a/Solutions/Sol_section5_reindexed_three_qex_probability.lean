-- Prove2me | solution 1 for section5_reindexed_three_qex_probability
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:12.158803+00:00
-- url     : https://prove2.me/submissions/db812daf-8720-42bb-a2da-5b230d421377

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
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5ReindexedQEXLaw
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_basis_permutation_probEvent
import Theorems.Thm_section5_three_qex_weighted_measurement
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_tensor_prob {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) (x : ι) (y : κ) :
    prob (tensorVec ψ φ) (x,y)=prob ψ x*prob φ y := by
  simp [prob,ket,EuclideanSpace.inner_single_left,tensorVec,mul_pow]











end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_ket_probability {ι : Type*} [Fintype ι] [DecidableEq ι] (a x : ι) :
    prob (ket a) x=if x=a then 1 else 0 := by
  by_cases h : a=x <;>
    simp [prob,ket,EuclideanSpace.inner_single_left,PiLp.single_apply,eq_comm,h]

theorem section5_three_qex_input_weighted_measurement {α : Type*} [Fintype α] [DecidableEq α]
    {n q : ℕ} (w : EuclideanSpace ℝ (Fin n)) (a : α)
    (G : α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)) → ℝ) :
    (∑ z, prob (tensorVec (ket a) (section5_three_qex_state (q:=q) w)) z*G z)=
      ∑ x, section5_three_qex_weight n q x*G (a,section5_labelled_three_qex_outcome w x) := by
  rw [Fintype.sum_prod_type]
  simp only [section5_tensor_prob,mul_assoc]
  simp_rw [← Finset.mul_sum]
  simp only [section5_ket_probability,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact section5_three_qex_weighted_measurement w (fun z => G (a,z))





end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership





theorem section5_reindex_probability {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (E : ι ≃ κ) (ψ : EuclideanSpace ℂ κ) (i : ι) :
    prob (section5_reindex_state E ψ) i=prob ψ (E i) := by
  simp only [prob,ket,EuclideanSpace.inner_single_left,map_one,one_mul,
    section5_reindex_state]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] {n q : ℕ}
    (E : ι ≃ α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)))
    (w : EuclideanSpace ℝ (Fin n)) (a : α)
    (U : Matrix ι ι ℂ) (F : Equiv.Perm ι) (hact : ∀ z, act U (ket z)=ket (F z))
    (P : ι → Prop) [DecidablePred P] :
    probEvent (act U (section5_reindex_state E
      (tensorVec (ket a) (section5_three_qex_state (q:=q) w)))) P=
      ∑ x, if P (F (E.symm (a,section5_labelled_three_qex_outcome w x))) then
        section5_three_qex_weight n q x else 0 := by
  rw [section5_basis_permutation_probEvent U F hact,← Equiv.sum_comp E.symm]
  simp only [section5_reindex_probability,Equiv.apply_symm_apply]
  have hh := section5_three_qex_input_weighted_measurement w a
    (fun z => if P (F (E.symm z)) then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero] using hh
