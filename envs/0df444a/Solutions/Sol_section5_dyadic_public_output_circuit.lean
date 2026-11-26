-- Prove2me | solution 1 for section5_dyadic_public_output_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:27.925788+00:00
-- url     : https://prove2.me/submissions/c391e3a0-24f9-418b-88ed-4f18eafd0f34

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
import Definitions.Def_Section5Verified_Section5DyadicBitOutput
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_dyadic_offset_bits_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! A clean reversible accumulator for an arbitrary binary weighted sum. The gate count
is linear in the accumulator width and the number of summands. -/











theorem section5_bitsToNatLSB_mod (w val : ℕ) :
    bitsToNatLSB (natToBitsLSB w val)=val%2^w := by
  have heq : natToBitsLSB w val=natToBitsLSB w (val%2^w) := by
    funext i
    simp [natToBitsLSB,Nat.testBit_mod_two_pow,i.isLt]
  rw [heq]
  exact bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))





end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Power-of-two division and offset-binary conversion by wire selection and
one complemented bit. This avoids general division in the output decoder. -/



theorem section5_shifted_bits_value {W : ℕ} (s w : ℕ) (hfit : s+w ≤ W) (z : Qubits W) :
    bitsToNatLSB (section5_shifted_bits s w hfit z)=(bitsToNatLSB z/2^s)%2^w := by
  have heq : section5_shifted_bits s w hfit z=natToBitsLSB w (bitsToNatLSB z/2^s) := by
    funext i
    have hz := congrFun (natToBitsLSB_bitsToNatLSB z) (⟨s+i.val,by omega⟩ : Fin W)
    simp only [natToBitsLSB] at hz ⊢
    change z ⟨s+i.val,by omega⟩=(bitsToNatLSB z/2^s).testBit i.val
    rw [← hz,Nat.testBit_div_two_pow]
    congr 1
    omega
  rw [heq,section5_bitsToNatLSB_mod]



theorem section5_offset_top_bit_value (b : ℕ) (z : Qubits (b+1)) :
    bitsToNatLSB (section5_offset_top_bit b z)=(bitsToNatLSB z+2^b)%2^(b+1) := by
  have hlow := bitsToNatLSB_lt b (fun i => z i.castSucc)
  have hN : bitsToNatLSB z=bitsToNatLSB (fun i : Fin b => z i.castSucc)+
      (if z (Fin.last b) then 2^b else 0) := by
    simp [bitsToNatLSB,Fin.sum_univ_castSucc]
  have hflip : bitsToNatLSB (section5_offset_top_bit b z)=
      bitsToNatLSB (fun i : Fin b => z i.castSucc)+(if !(z (Fin.last b)) then 2^b else 0) := by
    simp [section5_offset_top_bit,bitsToNatLSB,Fin.sum_univ_castSucc,Fin.castSucc_ne_last]
  rw [hN,hflip,pow_succ]
  cases hz : z (Fin.last b)
  · simp only [hz,Bool.false_eq_true,↓reduceIte,Bool.not_false,add_zero]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [hz,↓reduceIte,Bool.not_true,Bool.false_eq_true,add_zero]
    have heq : bitsToNatLSB (fun i : Fin b => z i.castSucc)+2^b+2^b=
        bitsToNatLSB (fun i : Fin b => z i.castSucc)+2^b*2 := by omega
    rw [heq,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]



theorem section5_dyadic_offset_bits_value {W : ℕ} (s b : ℕ) (hfit : s+(b+1) ≤ W)
    (z : Qubits W) :
    bitsToNatLSB (section5_dyadic_offset_bits s b hfit z)=
      (bitsToNatLSB z/2^s+2^b)%2^(b+1) := by
  rw [section5_dyadic_offset_bits,section5_offset_top_bit_value,section5_shifted_bits_value,
    Nat.mod_add_mod]



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

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Widening the output by one bit permits exact sign correction even at the most
negative input endpoint of the published offset-binary fixed-point encoding. -/







theorem section5_msb_binary_value {w : ℕ} (z : Qubits w) :
    bitsToNat (section5_lsb_to_msb z)=bitsToNatLSB z := by
  have hh := section5_reversed_binary_value (section5_lsb_to_msb z)
  simpa only [section5_lsb_to_msb,Fin.rev_rev] using hh.symm







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

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! The selected-bit output circuit implements signed power-of-two division and
the public fixed-point decoder exactly, including negative numerators. -/

theorem section5_signed_shift_mod (d s b : ℕ) (hfit : s+(b+1) ≤ d+1)
    (z : Qubits (d+1)) :
    ((section5_integer_bit_value (section5_twos_coefficient (d+1)) z)/(2:ℤ)^s)%(2:ℤ)^(b+1)=
      ((bitsToNatLSB z:ℤ)/(2:ℤ)^s)%(2:ℤ)^(b+1) := by
  have hp : (2:ℤ)^(d+1)=(2:ℤ)^s*((2:ℤ)^(b+1)*(2:ℤ)^(d+1-s-(b+1))) := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  rw [section5_twos_complement_value]
  cases hz : z (Fin.last d)
  · simp
  · simp only [↓reduceIte]
    rw [hp,Int.sub_mul_ediv_left _ _ (by positivity)]
    simp [Int.sub_emod,Int.mul_emod]

theorem section5_dyadic_offset_integer (d s b : ℕ) (hfit : s+(b+1) ≤ d+1)
    (z : Qubits (d+1))
    (hlo : -(2:ℤ)^b ≤ section5_integer_bit_value (section5_twos_coefficient (d+1)) z/(2:ℤ)^s)
    (hhi : section5_integer_bit_value (section5_twos_coefficient (d+1)) z/(2:ℤ)^s < (2:ℤ)^b) :
    (bitsToNatLSB (section5_dyadic_offset_bits s b hfit z):ℤ)=
      section5_integer_bit_value (section5_twos_coefficient (d+1)) z/(2:ℤ)^s+(2:ℤ)^b := by
  let V := section5_integer_bit_value (section5_twos_coefficient (d+1)) z/(2:ℤ)^s
  have hm := section5_signed_shift_mod d s b hfit z
  change V%(2:ℤ)^(b+1)=_ at hm
  calc
    _ = ((bitsToNatLSB z:ℤ)/(2:ℤ)^s+(2:ℤ)^b)%(2:ℤ)^(b+1) := by
      exact_mod_cast section5_dyadic_offset_bits_value s b hfit z
    _ = (V+(2:ℤ)^b)%(2:ℤ)^(b+1) := by
      rw [Int.add_emod,← hm,← Int.add_emod]
    _ = V+(2:ℤ)^b := Int.emod_eq_of_lt (by dsimp only [V]; omega)
      (by rw [pow_succ]; dsimp only [V]; omega)

theorem section5_dyadic_output_fpVal (d s b f : ℕ) (hfit : s+(b+1) ≤ d+1)
    (z : Qubits (d+1))
    (hlo : -(2:ℤ)^b ≤ section5_integer_bit_value (section5_twos_coefficient (d+1)) z/(2:ℤ)^s)
    (hhi : section5_integer_bit_value (section5_twos_coefficient (d+1)) z/(2:ℤ)^s < (2:ℤ)^b) :
    fpVal (b+1) f (section5_lsb_to_msb (section5_dyadic_offset_bits s b hfit z))=
      ((section5_integer_bit_value (section5_twos_coefficient (d+1)) z/(2:ℤ)^s:ℤ):ℝ)/(2:ℝ)^f := by
  have hvalue := section5_dyadic_offset_integer d s b hfit z hlo hhi
  have hreal : (bitsToNatLSB (section5_dyadic_offset_bits s b hfit z):ℝ)=
      ((section5_integer_bit_value (section5_twos_coefficient (d+1)) z/(2:ℤ)^s:ℤ):ℝ)+(2:ℝ)^b := by
    exact_mod_cast hvalue
  unfold fpVal
  rw [section5_msb_binary_value,hreal,pow_succ]
  ring



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m d b : ℕ}
    (src : Fin (d+1) ↪ Fin m) (dst : Fin (b+1) ↪ Fin m) (s : ℕ)
    (hfit : s+(b+1) ≤ d+1) (hdisj : ∀ i j, src i ≠ dst j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(b+1) ∧
      ∀ z : Qubits m, (∀ j, z (dst j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range dst → z' j=z j) ∧
          ∀ f : ℕ,
          -(2:ℤ)^b ≤ section5_integer_bit_value (section5_twos_coefficient (d+1)) (z ∘ src)/(2:ℤ)^s →
          section5_integer_bit_value (section5_twos_coefficient (d+1)) (z ∘ src)/(2:ℤ)^s < (2:ℤ)^b →
          readFp (⟨fun i => dst i.rev,fun _ _ h => Fin.rev_injective (dst.injective h)⟩) f z'=
            ((section5_integer_bit_value (section5_twos_coefficient (d+1)) (z ∘ src)/(2:ℤ)^s:ℤ):ℝ)/(2:ℝ)^f := by
  obtain ⟨c,hc,hact⟩ := section5_dyadic_offset_bits_circuit src dst s hfit hdisj
  refine ⟨c,hc,?_⟩
  intro z hz
  let z' := Thm410Router.updateOn dst z (section5_dyadic_offset_bits s b hfit (z ∘ src))
  have hbits : z' ∘ dst=section5_dyadic_offset_bits s b hfit (z ∘ src) := by
    funext i
    exact Thm410Router.updateOn_apply_emb dst z _ i
  refine ⟨z',hact z hz,fun j hj => Thm410Router.updateOn_apply_not_mem dst z _ hj,?_⟩
  intro f hlo hhi
  change fpVal (b+1) f (section5_lsb_to_msb (z' ∘ dst))=_
  rw [hbits]
  exact section5_dyadic_output_fpVal d s b f hfit (z ∘ src) hlo hhi
