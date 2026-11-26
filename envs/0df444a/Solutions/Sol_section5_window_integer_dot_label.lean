-- Prove2me | solution 1 for section5_window_integer_dot_label
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:11:03.56718+00:00
-- url     : https://prove2.me/submissions/97eca375-8609-42d1-a304-0b847a3ac094

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Definitions.Def_Section5Verified_Section5MiddleBits
import Definitions.Def_Section5Verified_Section5RealWindow
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Definitions.Def_Section5Verified_Section5WindowDotIdentity
import Mathlib
import Theorems.Thm_section5_middle_bits_twos_decoder
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership Aux_w_53_hermite

/-! The sampled phase vector is exactly the phase branch of the public QEX state. -/





theorem section5_gridPoint_flatReg {n q : ℕ} (z : Fin n → Qubits q) :
    gridPoint (flatReg n q z) = WithLp.toLp 2 (fun i => scalarGrid (z i)) := by
  have hflat (i : Fin n) : (fun j : Fin q => flatReg n q z
      ⟨i.val*q+j.val,by nlinarith [Nat.mul_le_mul_right q (Nat.succ_le_iff.mpr i.isLt),j.isLt]⟩) = z i := by
    funext j
    simpa only [flatReg,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using
      congrArg (fun p : Fin n × Fin q => z p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
  simp only [gridPoint,scalarGrid,hflat]















end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Exact integer comparison for orientation: Gaussian grid scaling and fixed-point denominators
are positive and cancel from the sign test. -/



theorem section5_binary_half_power (ℓ : ℕ) (hℓ : 0 < ℓ) :
    (2:ℝ)^ℓ/2=((2^(ℓ-1) : ℕ) : ℝ) := by
  rcases ℓ with _ | ℓ
  · omega
  simp only [Nat.add_sub_cancel,pow_succ,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem section5_fpVal_centered_integer {ℓ : ℕ} (hℓ : 0 < ℓ) (f : ℕ) (z : Qubits ℓ) :
    fpVal ℓ f z=(section5_centered_integer z : ℝ)/(2:ℝ)^f := by
  unfold fpVal section5_centered_integer
  rw [section5_binary_half_power ℓ hℓ]
  push_cast
  rfl

theorem section5_scalarGrid_centered_integer {q : ℕ} (z : Qubits q) :
    scalarGrid z=(section5_centered_integer z : ℝ)*gridSpacing (2^q) := by
  unfold scalarGrid section5_centered_integer gridSpacing
  simp only [QuantumLTF.Example.bitsValue,bitsToNat,Int.cast_sub,Int.cast_natCast,
    Nat.cast_pow,Nat.cast_ofNat]
  push_cast
  rfl









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















theorem section5_scalarGrid_window {q : ℕ} (z : Qubits q) (P H : ℤ) :
    section5_real_window P H (QuantumLTF.Example.gridSpacing (2^q))
      (QuantumLTF.Example.scalarGrid z)=
        QuantumLTF.Example.gridSpacing (2^q)*
          (section5_window_truncate P H (section5_centered_integer z):ℝ) := by
  rw [section5_scalarGrid_centered_integer]
  unfold section5_real_window
  have hδ : QuantumLTF.Example.gridSpacing (2^q) ≠ 0 :=
    ne_of_gt (section5_gridSpacing_positive _ (Nat.two_pow_pos q))
  rw [mul_div_cancel_right₀ _ hδ,Int.floor_intCast]

end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives

/-! The bounded-precision sign comparison is an exact integer dot product using the
public fixed-point and Gaussian-grid encodings. -/

theorem section5_fpVal_offset_lsb (a f : ℕ) (z : Qubits (a+1)) :
    fpVal (a+1) f z=
      (((bitsToNatLSB (fun j => z j.rev):ℤ)-(2:ℤ)^a : ℤ):ℝ)/(2:ℝ)^f := by
  rw [section5_fpVal_centered_integer (by omega) f]
  unfold section5_centered_integer
  rw [section5_reversed_binary_value]
  simp only [Nat.add_sub_cancel,Int.natCast_pow,Nat.cast_ofNat]

theorem section5_gridPoint_coordinate {n q : ℕ} (z : Qubits (n*q)) (i : Fin n) :
    gridPoint z i=scalarGrid (splitReg n q z i) := by
  have hh := section5_gridPoint_flatReg (splitReg n q z)
  have hflat : flatReg n q (splitReg n q z)=z := (section5_register_equiv n q).apply_symm_apply z
  rw [hflat] at hh
  exact congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) hh

theorem section5_window_grid_coordinate {n q : ℕ} (z : Qubits (n*q)) (i : Fin n)
    (s b : ℕ) (h : s+(b+1) ≤ q-1) :
    section5_real_window_vec ((2:ℤ)^s) ((2:ℤ)^b) (gridSpacing (2^q)) (gridPoint z) i=
      (gridSpacing (2^q)*(2:ℝ)^s)*
        (section5_integer_bit_value (section5_twos_coefficient (b+1))
          (section5_middle_bits (splitReg n q z i) s (b+1) (by omega)):ℝ) := by
  change section5_real_window ((2:ℤ)^s) ((2:ℤ)^b) (gridSpacing (2^q)) (gridPoint z i)=_
  rw [section5_gridPoint_coordinate,section5_scalarGrid_window,
    section5_middle_bits_twos_decoder (splitReg n q z i) s b h]
  push_cast
  ring



theorem section5_window_integer_dot_identity {n q a : ℕ} (f : ℕ)
    (u : Fin n → Qubits (a+1)) (z : Qubits (n*q))
    (s b : ℕ) (h : s+(b+1) ≤ q-1) :
    inner ℝ (WithLp.toLp 2 (fun i => fpVal (a+1) f (u i)))
      (section5_real_window_vec ((2:ℤ)^s) ((2:ℤ)^b) (gridSpacing (2^q)) (gridPoint z))=
        (gridSpacing (2^q)*(2:ℝ)^s/(2:ℝ)^f)*
          (section5_window_integer_dot u z s b h : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i : Fin n, _*fpVal (a+1) f (u i))=_
  simp_rw [section5_window_grid_coordinate z _ s b h,section5_fpVal_offset_lsb]
  unfold section5_window_integer_dot
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives
theorem solution {n q a : ℕ} (f : ℕ)
    (u : Fin n → Qubits (a+1)) (z : Qubits (n*q))
    (s b : ℕ) (h : s+(b+1) ≤ q-1) :
    ltf (WithLp.toLp 2 (fun i => fpVal (a+1) f (u i))) 0
      (section5_real_window_vec ((2:ℤ)^s) ((2:ℤ)^b) (gridSpacing (2^q)) (gridPoint z))=
        sgn (section5_window_integer_dot u z s b h : ℝ) := by
  unfold ltf
  rw [sub_zero,section5_window_integer_dot_identity f u z s b h]
  have hc : 0 < gridSpacing (2^q)*(2:ℝ)^s/(2:ℝ)^f := by
    apply div_pos (mul_pos (section5_gridSpacing_positive _ (Nat.two_pow_pos q)) (by positivity))
    positivity
  unfold sgn
  simp only [mul_nonneg_iff_of_pos_left hc]
