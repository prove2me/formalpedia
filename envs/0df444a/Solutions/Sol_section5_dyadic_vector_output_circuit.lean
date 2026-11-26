-- Prove2me | solution 1 for section5_dyadic_vector_output_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:15:58.98071+00:00
-- url     : https://prove2.me/submissions/f346a6cb-2db1-4b14-964e-f11850c3c519

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
import Definitions.Def_Section5Verified_Section5DyadicVectorOutput
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_dyadic_floor
import Theorems.Thm_section5_dyadic_vector_bits_circuit
import Theorems.Thm_section5_quantize_decode
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
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! The dyadic wire-selection circuit implements the same floor quantization
used in the analytic reconstruction guarantee, including negative coordinates. -/



theorem section5_dyadic_quotient_range (S f : ℕ) (hf : f ≤ S) (v : ℤ)
    (hv : |((2:ℝ)^S)⁻¹*(v:ℝ)| ≤ 1) :
    -(2:ℤ)^(f+1) ≤ v/(2:ℤ)^(S-f) ∧ v/(2:ℤ)^(S-f) < (2:ℤ)^(f+1) := by
  rw [← section5_dyadic_floor S f hf v]
  have hp : (0:ℝ) < 2^f := by positivity
  have hlo : -(2:ℤ)^f ≤ ⌊(2:ℝ)^f*(((2:ℝ)^S)⁻¹*(v:ℝ))⌋ := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith [(abs_le.mp hv).1]
  have hhi : ⌊(2:ℝ)^f*(((2:ℝ)^S)⁻¹*(v:ℝ))⌋ ≤ (2:ℤ)^f := by
    have hh : (2:ℝ)^f*(((2:ℝ)^S)⁻¹*(v:ℝ)) ≤ ((2:ℤ)^f:ℝ) := by
      push_cast
      nlinarith [(abs_le.mp hv).2]
    have hfloor := (Int.floor_le ((2:ℝ)^f*(((2:ℝ)^S)⁻¹*(v:ℝ)))).trans hh
    exact_mod_cast hfloor
  rw [pow_succ]
  have hpow : (0:ℤ) < 2^f := by positivity
  omega

theorem section5_dyadic_bits_quantize (d S f : ℕ) (hf : f ≤ S)
    (hfit : S-f+(f+1+1) ≤ d+1) (z : Qubits (d+1))
    (hz : |((2:ℝ)^S)⁻¹*
      (section5_integer_bit_value (section5_twos_coefficient (d+1)) z:ℝ)| ≤ 1) :
    fpVal (f+2) f
        (section5_lsb_to_msb (section5_dyadic_offset_bits (S-f) (f+1) hfit z))=
      fpVal (f+2) f (section5_quantize_bits f (((2:ℝ)^S)⁻¹*
        (section5_integer_bit_value (section5_twos_coefficient (d+1)) z:ℝ))) := by
  have hr := section5_dyadic_quotient_range S f hf _ hz
  rw [section5_dyadic_output_fpVal d (S-f) (f+1) f hfit z hr.1 hr.2,
    section5_quantize_decode f _ hz,section5_dyadic_floor S f hf]







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m r N d S f : ℕ}
    (data : Fin r ↪ Fin m) (src : Fin N → Fin (d+1) ↪ Fin r)
    (dst : Fin N → Fin (f+2) ↪ Fin m) (hf : f ≤ S) (hfit : S-f+(f+1+1) ≤ d+1)
    (hpair : ∀ i j, i ≠ j → ∀ e b, dst i e ≠ dst j b)
    (hdata : ∀ i j e, data j ≠ dst i e) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(f+2)*N ∧
      ∀ z : Qubits m, (∀ i e, z (dst i e)=false) →
        (∀ i, |section5_signed_dyadic_vector src S (z ∘ data) i| ≤ 1) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (dst i)) → z' j=z j) ∧
          (WithLp.toLp 2 fun i => readFp
            (⟨fun e => dst i e.rev,fun _ _ h => Fin.rev_injective ((dst i).injective h)⟩)
            f z')=section5_quantize_vector f (section5_signed_dyadic_vector src S (z ∘ data)) := by
  obtain ⟨c,hc,hact⟩ := section5_dyadic_vector_bits_circuit data src dst (S-f) hfit hpair hdata
  refine ⟨c,hc,?_⟩
  intro z hz0 hz
  obtain ⟨z',hz',hoff,hbits⟩ := hact z hz0
  refine ⟨z',hz',hoff,?_⟩
  ext i
  change fpVal (f+2) f (section5_lsb_to_msb (z' ∘ dst i))=
    fpVal (f+2) f (section5_quantize_bits f _)
  rw [hbits i]
  exact section5_dyadic_bits_quantize d S f hf hfit _ (hz i)
