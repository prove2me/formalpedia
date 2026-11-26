-- Prove2me | solution 1 for section5_signed_dot_no_overflow
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:37.567796+00:00
-- url     : https://prove2.me/submissions/975eb557-b061-49e4-9bad-3bf29833a30c

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
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_twos_complement_residue
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! A complete signed dot-product comparator with an explicit polynomial gate bound.
The accumulator width below is deliberately generous, to make overflow impossible. -/

theorem section5_signed_residue_range (H z : ℤ) (hH : 0 < H) :
    -H ≤ section5_signed_residue H z ∧ section5_signed_residue H z < H := by
  have hlo := Int.emod_nonneg z (by positivity : 2*H ≠ 0)
  have hhi := Int.emod_lt_of_pos z (by positivity : 0 < 2*H)
  unfold section5_signed_residue
  split_ifs <;> constructor <;> omega

theorem section5_twos_complement_abs (b : ℕ) (z : Qubits (b+1)) :
    |section5_integer_bit_value (section5_twos_coefficient (b+1)) z| ≤ (2:ℤ)^b := by
  rw [section5_twos_complement_residue]
  have hh := section5_signed_residue_range ((2:ℤ)^b) (bitsToNatLSB z) (by positivity)
  exact abs_le.mpr ⟨hh.1,hh.2.le⟩





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
theorem solution {n a b : ℕ}
    (u : Fin n → Qubits (a+1)) (x : Fin n → Qubits (b+1)) :
    |∑ i : Fin n, section5_integer_bit_value (section5_twos_coefficient (a+1)) (u i)*
      section5_integer_bit_value (section5_twos_coefficient (b+1)) (x i)| < (2:ℤ)^(n+a+b) := by
  calc
    _ ≤ ∑ i : Fin n,
        |section5_integer_bit_value (section5_twos_coefficient (a+1)) (u i)*
          section5_integer_bit_value (section5_twos_coefficient (b+1)) (x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (2:ℤ)^a*(2:ℤ)^b := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (section5_twos_complement_abs a (u i))
        (section5_twos_complement_abs b (x i)) (abs_nonneg _) (by positivity)
    _ = (n:ℤ)*(2:ℤ)^(a+b) := by simp [pow_add]
    _ < (2:ℤ)^n*(2:ℤ)^(a+b) := by
      apply mul_lt_mul_of_pos_right _ (by positivity)
      exact_mod_cast (Nat.lt_two_pow_self (n:=n))
    _ = _ := by rw [← pow_add]; congr 1; omega
