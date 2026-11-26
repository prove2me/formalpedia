-- Prove2me | solution 1 for section5_fixed_point_output_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:27.486487+00:00
-- url     : https://prove2.me/submissions/e3294418-83a0-49e8-921d-628a4fe084ed

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
import Definitions.Def_Section5Verified_Section5AffineCopy
import Definitions.Def_Section5Verified_Section5ConditionalNegation
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
import Theorems.Thm_section5_affine_copy_circuit
import Theorems.Thm_section5_conditional_negation_circuit
import Theorems.Thm_section5_signed_fixed_point_output
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! A complete reversible sign-output circuit for the public fixed-point encoding.
One extra output bit avoids overflow at the most negative input endpoint. -/



theorem section5_widen_bits_value (a : ℕ) (x : Qubits (a+1)) :
    bitsToNatLSB (section5_widen_bits a x)=bitsToNatLSB x+2^a := by
  simp only [section5_widen_bits,bitsToNatLSB,Fin.sum_univ_castSucc,
    Fin.snoc_castSucc,Fin.snoc_last,Fin.val_castSucc,Fin.val_last]
  cases hx : x (Fin.last a) <;> simp [hx,pow_succ] <;> omega





theorem section5_widen_affine_bits {m : ℕ} (a : ℕ) (p : Fin (a+1) ↪ Fin m)
    (z : Qubits m) :
    section5_affine_bit (section5_widen_source a p) (section5_widen_invert a) z=
      section5_widen_bits a (z ∘ p) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [section5_affine_bit,section5_widen_source,section5_widen_invert,section5_widen_bits]
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [section5_affine_bit,section5_widen_source,section5_widen_invert,section5_widen_bits]
    · simp [section5_affine_bit,section5_widen_source,section5_widen_invert,section5_widen_bits,
        Fin.castSucc_ne_last]



theorem section5_msb_read {m w : ℕ} (p : Fin w ↪ Fin m) (f : ℕ) (z : Qubits m) :
    readFp (section5_msb_register p) f z=fpVal w f (section5_lsb_to_msb (z ∘ p)) := rfl

theorem section5_widen_signed_bits_value (a : ℕ) (x : Qubits (a+1)) :
    2^(a+2)-bitsToNatLSB (section5_widen_bits a x)=
      section5_signed_output_integer a (bitsToNatLSB x) true := by
  rw [section5_widen_bits_value]
  have hx := bitsToNatLSB_lt (a+1) x
  have hM : 2^(a+2)=4*2^a := by rw [show a+2=a+1+1 by omega,pow_succ,pow_succ]; ring
  rw [hM]
  simp only [section5_signed_output_integer,↓reduceIte]
  rw [pow_succ] at hx
  omega



end
section
set_option autoImplicit false

open QAlgorithms Thm49Primitives

/-! Exact extraction of a bounded window from the published most-significant-bit-first
register encoding. This only reads the selected wires, regardless of the full precision. -/

theorem section5_reversed_binary_value {q : ℕ} (z : Qubits q) :
    bitsToNatLSB (fun i => z i.rev)=bitsToNat z := by
  unfold bitsToNatLSB bitsToNat
  calc
    _ = ∑ i : Fin q, if z i.rev then 2^(q-1-i.rev.val) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have heq : q-1-i.rev.val=i.val := by simp only [Fin.val_rev]; omega
      rw [heq]
    _ = _ := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin q))
      (fun i : Fin q => if z i then (2:ℕ)^(q-1-i.val) else 0)

















end
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
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Widening the output by one bit permits exact sign correction even at the most
negative input endpoint of the published offset-binary fixed-point encoding. -/







theorem section5_msb_binary_value {w : ℕ} (z : Qubits w) :
    bitsToNat (section5_lsb_to_msb z)=bitsToNatLSB z := by
  have hh := section5_reversed_binary_value (section5_lsb_to_msb z)
  simpa only [section5_lsb_to_msb,Fin.rev_rev] using hh.symm







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
theorem solution {m : ℕ} (a f : ℕ) (ctrl : Fin m)
    (input : Fin (a+1) ↪ Fin m) (output : Fin (a+2) ↪ Fin m)
    (anc : Fin (a+3) ↪ Fin m)
    (hio : ∀ i j, input i ≠ output j)
    (hco : ∀ i, ctrl ≠ output i) (hca : ∀ i, ctrl ≠ anc i)
    (hoa : ∀ i j, output i ≠ anc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 19*(a+2) ∧
      ∀ z : Qubits m, (∀ i, z (output i)=false) → (∀ i, z (anc i)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range output → z' j=z j) ∧
          readFp (section5_msb_register output) f z'=
            if z ctrl then -readFp (section5_msb_register input) f z
              else readFp (section5_msb_register input) f z := by
  classical
  have hs : ∀ i j, section5_widen_source a input i ≠ output j := by
    intro i j
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa only [section5_widen_source,Fin.lastCases_last] using hio (Fin.last a) j
    · simpa only [section5_widen_source,Fin.lastCases_castSucc] using hio k j
  obtain ⟨c,hc,hact⟩ := section5_affine_copy_circuit
    (section5_widen_source a input) output (section5_widen_invert a) hs
  obtain ⟨d,hd,hdact⟩ := section5_conditional_negation_circuit (by omega : 0 < a+2)
    ctrl output anc hco hca hoa
  refine ⟨c++d,?_,?_⟩
  · simp only [Circuit.size,List.length_append]
    change c.length ≤ _ at hc
    change d.length ≤ _ at hd
    omega
  · intro z hzo hza
    let x := z ∘ input
    let z1 := updateOn output z (section5_widen_bits a x)
    have hz1off (j : Fin m) (hj : j ∉ Set.range output) : z1 j=z j :=
      updateOn_apply_not_mem output z _ hj
    have hz1anc (i : Fin (a+3)) : z1 (anc i)=false :=
      (hz1off _ (by rintro ⟨j,hj⟩; exact hoa j i hj)).trans (hza i)
    have hz1ctrl : z1 ctrl=z ctrl := hz1off _ (by rintro ⟨i,hi⟩; exact hco i hi.symm)
    have hz1out : z1 ∘ output=section5_widen_bits a x := by
      funext i
      exact updateOn_apply_emb output z _ i
    let z2 := section5_conditional_negate ctrl output z1
    have hz2off (j : Fin m) (hj : j ∉ Set.range output) : z2 j=z j := by
      dsimp only [z2,section5_conditional_negate]
      split_ifs
      · exact (updateOn_apply_not_mem output z1 _ hj).trans (hz1off j hj)
      · exact hz1off j hj
    have hz2out : z2 ∘ output=natToBitsLSB (a+2)
        (section5_signed_output_integer a (bitsToNatLSB x) (z ctrl)) := by
      dsimp only [z2,section5_conditional_negate]
      rw [hz1ctrl]
      cases hzc : z ctrl
      · simp only [Bool.false_eq_true,↓reduceIte,section5_signed_output_integer]
        rw [hz1out,← section5_widen_bits_value,natToBitsLSB_bitsToNatLSB]
      · simp only [↓reduceIte]
        funext i
        simp only [Function.comp_apply]
        rw [updateOn_apply_emb,hz1out,section5_widen_signed_bits_value]
    refine ⟨z2,?_,hz2off,?_⟩
    · rw [section5_boolean_circuit_append,hact z hzo,section5_widen_affine_bits,hdact z1 hz1anc]
    · rw [section5_msb_read,section5_msb_read,hz2out]
      have hx : bitsToNat (section5_lsb_to_msb x)=bitsToNatLSB x := section5_msb_binary_value x
      simpa only [hx] using section5_signed_fixed_point_output a f (section5_lsb_to_msb x) (z ctrl)
