-- Prove2me | solution 1 for section5_majority_sign_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:18:10.075615+00:00
-- url     : https://prove2.me/submissions/c4892ad3-ffdc-4074-acb8-218db7fbef3e

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
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5MajorityCircuit
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Mathlib
import Theorems.Thm_section5_majority_circuit_action
import Theorems.Thm_section5_vector_sign_output_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/































































theorem section5_boolean_circuit_append {m : ℕ} (c d : Circuit gatesRev m)
    (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary (c++d)) ψ=act d.unitary (act c.unitary ψ) := by
  classical
  ext z
  simp only [Circuit.unitary,List.map_append,List.reverse_append,List.prod_append]
  exact congrFun (Matrix.mulVec_mulVec ψ _ _).symm z









end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {m n : ℕ} (a f : ℕ)
    (votes : Fin 3 ↪ Fin m) (ctrl : Fin m) (ht : ctrl ∉ Set.range votes)
    (input : Fin n → Fin (a+1) ↪ Fin m) (output : Fin n → Fin (a+2) ↪ Fin m)
    (anc : Fin (a+3) ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e b, output i e ≠ output j b)
    (hio : ∀ i j e b, input i e ≠ output j b)
    (hco : ∀ i e, ctrl ≠ output i e) (hca : ∀ e, ctrl ≠ anc e)
    (hoa : ∀ i e b, output i e ≠ anc b) (hic : ∀ i e, input i e ≠ ctrl) :
    ∃ c : Circuit gatesRev m, c.size ≤ 3+19*(a+2)*n ∧
      ∀ z : Qubits m, z ctrl=false → (∀ e, z (anc e)=false) → (∀ i e, z (output i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ≠ ctrl → (∀ i, j ∉ Set.range (output i)) → z' j=z j) ∧
          (WithLp.toLp 2 fun i => readFp (section5_msb_register (output i)) f z')=
            if section5_majority_bit (z (votes 0)) (z (votes 1)) (z (votes 2)) then
              -(WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z)
            else (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z) := by
  classical
  obtain ⟨co,ho,hoa'⟩ := section5_vector_sign_output_circuit a f ctrl input output anc
    hpair hio hco hca hoa
  let cm := section5_majority_circuit votes ctrl ht
  have hcm : cm.length=3 := rfl
  refine ⟨cm++co,?_,?_⟩
  · simpa only [Circuit.size,List.length_append,hcm] using
      Nat.add_le_add_left ho 3
  · intro z hzc hza hzo
    let bit := section5_majority_bit (z (votes 0)) (z (votes 1)) (z (votes 2))
    let z1 := Function.update z ctrl bit
    have hz1 : act cm.unitary (ket z)=ket z1 := by
      rw [section5_majority_circuit_action,hzc,Bool.false_xor]
    have hz1anc : ∀ e, z1 (anc e)=false := by
      intro e
      exact (Function.update_of_ne (hca e).symm _ _).trans (hza e)
    have hz1out : ∀ i e, z1 (output i e)=false := by
      intro i e
      exact (Function.update_of_ne (hco i e).symm _ _).trans (hzo i e)
    have hinput (i : Fin n) :
        readFp (section5_msb_register (input i)) f z1=readFp (section5_msb_register (input i)) f z := by
      apply congrArg (fpVal (a+1) f)
      funext e
      exact Function.update_of_ne (hic i e.rev) _ _
    obtain ⟨z2,hz2,hoff,hval⟩ := hoa' z1 hz1anc hz1out
    refine ⟨z2,?_,?_,?_⟩
    · rw [section5_boolean_circuit_append,hz1,hz2]
    · intro j hj hc
      exact (hoff j hc).trans (Function.update_of_ne hj _ _)
    · have hbit : z1 ctrl=bit := Function.update_self _ _ _
      rw [hbit] at hval
      have hvec : (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z1)=
          (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z) := by
        ext i
        exact hinput i
      rw [hvec] at hval
      exact hval
