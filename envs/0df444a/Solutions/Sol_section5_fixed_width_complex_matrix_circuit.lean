-- Prove2me | solution 1 for section5_fixed_width_complex_matrix_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:23:24.233554+00:00
-- url     : https://prove2.me/submissions/4a5b444c-0f40-4b27-bcd1-37b29b5f728a

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5ModularMatrixCircuit
import Definitions.Def_Section5Verified_Section5ModularMatrixPowers
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_complex_matrix_product_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! A full complex integer matrix multiplication compiled to the actual reversible
gate set. The input and shared workspace are preserved. -/

















theorem section5_complex_matrix_gate_bound (n a b w : ℕ) (hw : 1 ≤ w) :
    ((16*w+6)*((n+n)*a*b))*(2*n*n) ≤ 88*w*n^3*a*b := by
  have hh : 16*w+6 ≤ 22*w := by omega
  calc
    _ ≤ (22*w)*((n+n)*a*b)*(2*n*n) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hh)
    _ = _ := by ring





end
section
set_option autoImplicit false

open QAlgorithms Thm49Primitives

/-! The bounded-window integer decoder is exactly the standard signed binary
linear form. This connects the window analysis to the signed dot-product circuit. -/



theorem section5_twos_complement_value (b : ℕ) (z : Qubits (b+1)) :
    section5_integer_bit_value (section5_twos_coefficient (b+1)) z=
      (bitsToNatLSB z : ℤ)-(if z (Fin.last b) then (2:ℤ)^(b+1) else 0) := by
  unfold section5_integer_bit_value section5_twos_coefficient bitsToNatLSB
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.add_left_inj,↓reduceIte]
  push_cast
  have hi (i : Fin b) : i.val ≠ b := by omega
  simp_rw [if_neg (hi _)]
  cases hz : z (Fin.last b) <;> simp [hz,pow_succ] <;> ring











end
section
set_option autoImplicit false

open QAlgorithms Thm49Primitives

/-! Modular complex matrix powers. Working modulo a fixed output width avoids
an increase in register width at each multiplication. Signed decoding agrees with
the same residues; only the final integer output needs an overflow bound. -/











theorem section5_integer_matrix_residue_mul {n : ℕ} (A B : Section5IntegerMatrix n) (w : ℕ) :
    (A.mul B).residue w=(A.residue w).mul (B.residue w) := by
  apply Section5ModMatrix.ext <;> funext i j <;>
    simp [Section5IntegerMatrix.residue,Section5IntegerMatrix.mul,Section5ModMatrix.mul,
      Matrix.mul_apply,Int.cast_sub,Int.cast_add,Int.cast_sum,Int.cast_mul] <;> rfl





theorem section5_signed_binary_residue (b : ℕ) (z : Qubits (b+1)) :
    (section5_integer_bit_value (section5_twos_coefficient (b+1)) z:ZMod (2^(b+1)))=
      (bitsToNatLSB z:ZMod (2^(b+1))) := by
  rw [section5_twos_complement_value]
  have hp : (((2:ℤ)^(b+1):ℤ):ZMod (2^(b+1)))=0 := by
    simpa only [Int.cast_pow,Int.cast_ofNat,Nat.cast_pow,Nat.cast_ofNat] using
      (ZMod.natCast_self (2^(b+1)))
  cases z (Fin.last b) <;> simp [hp]





theorem section5_mod_matrix_components_ext {n w : ℕ}
    (v u : Fin (2*n*n) → ZMod (2^w)) (h : ∀ i, v i=u i) :
    section5_mod_matrix_from_components v=section5_mod_matrix_from_components u := by
  congr 1
  exact funext h



theorem section5_mod_matrix_product_components {n w : ℕ} (A B : Section5IntegerMatrix n) :
    section5_mod_matrix_from_components (fun i =>
      (section5_complex_product_component A B (section5_complex_entry_index n i):ZMod (2^w)))=
        (A.residue w).mul (B.residue w) := by
  rw [← section5_integer_matrix_residue_mul]
  apply Section5ModMatrix.ext <;> funext i j <;>
    simp [section5_mod_matrix_from_components,section5_complex_product_component,
      Section5IntegerMatrix.residue]

end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Matrix multiplication at a fixed bit width, with explicit source/output wire
registers. This is the step used to iterate matrix powers with bounded storage. -/







theorem section5_matrix_source_wire_on {m n w : ℕ}
    (A B : Fin (2*n*n) → Fin w ↪ Fin m) (side im : Bool) (i j : Fin n) (b : Fin w) :
    section5_matrix_source_wire A B (section5_matrix_source_bits n w side im i j b)=
      if side then B ((section5_complex_entry_index n).symm (im,i,j)) b
        else A ((section5_complex_entry_index n).symm (im,i,j)) b := by
  simp [section5_matrix_source_wire,section5_matrix_source_bits]

theorem section5_matrix_source_residue {m n b : ℕ}
    (A B : Fin (2*n*n) → Fin (b+1) ↪ Fin m) (side : Bool) (z : Qubits m) :
    (section5_read_integer_matrix (section5_twos_coefficient (b+1))
      (section5_matrix_source_bits n (b+1) side false)
      (section5_matrix_source_bits n (b+1) side true)
      (z ∘ section5_matrix_source_wire A B)).residue (b+1)=
        section5_mod_matrix_read (if side then B else A) z := by
  apply Section5ModMatrix.ext <;> funext i j
  · have hbits : (z ∘ section5_matrix_source_wire A B) ∘ section5_matrix_source_bits n (b+1) side false i j=
        z ∘ (if side then B else A) ((section5_complex_entry_index n).symm (false,i,j)) := by
      funext k
      simp only [Function.comp_apply,section5_matrix_source_wire_on]
      cases side <;> rfl
    change (section5_integer_bit_value (section5_twos_coefficient (b+1))
      ((z ∘ section5_matrix_source_wire A B) ∘ section5_matrix_source_bits n (b+1) side false i j):
        ZMod (2^(b+1)))=(bitsToNatLSB
          (z ∘ (if side then B else A) ((section5_complex_entry_index n).symm (false,i,j))):ZMod (2^(b+1)))
    rw [hbits,section5_signed_binary_residue]
  · have hbits : (z ∘ section5_matrix_source_wire A B) ∘ section5_matrix_source_bits n (b+1) side true i j=
        z ∘ (if side then B else A) ((section5_complex_entry_index n).symm (true,i,j)) := by
      funext k
      simp only [Function.comp_apply,section5_matrix_source_wire_on]
      cases side <;> rfl
    change (section5_integer_bit_value (section5_twos_coefficient (b+1))
      ((z ∘ section5_matrix_source_wire A B) ∘ section5_matrix_source_bits n (b+1) side true i j):
        ZMod (2^(b+1)))=(bitsToNatLSB
          (z ∘ (if side then B else A) ((section5_complex_entry_index n).symm (true,i,j))):ZMod (2^(b+1)))
    rw [hbits,section5_signed_binary_residue]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m n b : ℕ}
    (A B p : Fin (2*n*n) → Fin (b+1) ↪ Fin m)
    (anc : Fin (b+1+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hAp : ∀ i j e f, A i e ≠ p j f) (hBp : ∀ i j e f, B i e ≠ p j f)
    (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j)
    (hAt : ∀ i e, A i e ≠ t) (hBt : ∀ i e, B i e ≠ t) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ 88*n^3*(b+1)^3 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          section5_mod_matrix_read p z'=
            (section5_mod_matrix_read A z).mul (section5_mod_matrix_read B z) := by
  classical
  let data := section5_matrix_source_wire A B
  let Are := section5_matrix_source_bits n (b+1) false false
  let Aim := section5_matrix_source_bits n (b+1) false true
  let Bre := section5_matrix_source_bits n (b+1) true false
  let Bim := section5_matrix_source_bits n (b+1) true true
  have hdata : ∀ i j e, data j ≠ p i e := by
    intro i j e
    dsimp only [data,section5_matrix_source_wire]
    split_ifs
    · exact hBp _ i _ e
    · exact hAp _ i _ e
  have hdt : ∀ j, data j ≠ t := by
    intro j
    dsimp only [data,section5_matrix_source_wire]
    split_ifs
    · exact hBt _ _
    · exact hAt _ _
  obtain ⟨circ,hsize,hact⟩ := section5_complex_matrix_product_circuit data
    (section5_twos_coefficient (b+1)) (section5_twos_coefficient (b+1))
    Are Aim Bre Bim p anc t hpair hdata hpa htp hta hdt
  have hcost := section5_complex_matrix_gate_bound n (b+1) (b+1) (b+1) (by omega)
  have hcost' : ((16*(b+1)+6)*((n+n)*(b+1)*(b+1)))*(2*n*n) ≤ 88*n^3*(b+1)^3 := by
    convert hcost using 1 <;> ring
  refine ⟨circ,hsize.trans hcost',?_⟩
  intro z hzt hza hz0
  obtain ⟨z',hz',hoff,hval⟩ := hact z hzt hza hz0
  refine ⟨z',hz',hoff,?_⟩
  let Ai := section5_read_integer_matrix (section5_twos_coefficient (b+1)) Are Aim (z ∘ data)
  let Bi := section5_read_integer_matrix (section5_twos_coefficient (b+1)) Bre Bim (z ∘ data)
  have hout : section5_mod_matrix_read p z'=(Ai.residue (b+1)).mul (Bi.residue (b+1)) := by
    unfold section5_mod_matrix_read
    rw [section5_mod_matrix_components_ext _ _ hval]
    exact section5_mod_matrix_product_components Ai Bi
  have hAi : Ai.residue (b+1)=section5_mod_matrix_read A z :=
    section5_matrix_source_residue A B false z
  have hBi : Bi.residue (b+1)=section5_mod_matrix_read B z :=
    section5_matrix_source_residue A B true z
  rw [hout,hAi,hBi]
