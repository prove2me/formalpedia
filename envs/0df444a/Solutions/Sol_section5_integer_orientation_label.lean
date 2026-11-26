-- Prove2me | solution 1 for section5_integer_orientation_label
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:50.078262+00:00
-- url     : https://prove2.me/submissions/253b311c-dc93-47fe-b195-1bad82a411c8

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Mathlib
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



theorem section5_integer_orientation_identity {n q ℓ : ℕ} (hℓ : 0 < ℓ) (f : ℕ)
    (u : Fin n → Qubits ℓ) (x : Qubits (n*q)) :
    inner ℝ (WithLp.toLp 2 (fun i => fpVal ℓ f (u i))) (gridPoint x) =
      (gridSpacing (2^q)/(2:ℝ)^f)*(section5_integer_orientation_dot u x : ℝ) := by
  have hx := section5_gridPoint_flatReg (splitReg n q x)
  have hflat : flatReg n q (splitReg n q x)=x := (section5_register_equiv n q).apply_symm_apply x
  rw [hflat] at hx
  rw [hx,EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, scalarGrid (splitReg n q x i)*fpVal ℓ f (u i)) = _
  simp_rw [section5_fpVal_centered_integer hℓ f,section5_scalarGrid_centered_integer]
  unfold section5_integer_orientation_dot
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n q ℓ : ℕ} (hℓ : 0 < ℓ) (f : ℕ)
    (u : Fin n → Qubits ℓ) (x : Qubits (n*q)) :
    ltf (WithLp.toLp 2 (fun i => fpVal ℓ f (u i))) 0 (gridPoint x) =
      sgn (section5_integer_orientation_dot u x : ℝ) := by
  unfold ltf
  rw [sub_zero,section5_integer_orientation_identity hℓ f u x]
  have hc : 0 < gridSpacing (2^q)/(2:ℝ)^f :=
    div_pos (section5_gridSpacing_positive (2^q) (Nat.two_pow_pos q)) (by positivity)
  unfold sgn
  simp only [mul_nonneg_iff_of_pos_left hc]
