-- Prove2me | solution 1 for section5_integer_matrix_residue_power
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:25.842795+00:00
-- url     : https://prove2.me/submissions/537156b4-1899-4434-9598-3ef88b13dbf9

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
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5ModularMatrixPowers
import Mathlib
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

theorem section5_integer_matrix_residue_one (n w : ℕ) :
    (Section5IntegerMatrix.one n).residue w=Section5ModMatrix.one n w := by
  apply Section5ModMatrix.ext <;> funext i j <;>
    by_cases h : i=j <;>
    simp [Section5IntegerMatrix.residue,Section5IntegerMatrix.one,Section5ModMatrix.one,Matrix.one_apply,h]















end
set_option autoImplicit false
open QAlgorithms Thm49Primitives
theorem solution {n : ℕ} (A : Section5IntegerMatrix n) (w k : ℕ) :
    (A.power k).residue w=(A.residue w).power k := by
  induction k with
  | zero => exact section5_integer_matrix_residue_one n w
  | succ k ih =>
    rw [Section5IntegerMatrix.power,section5_integer_matrix_residue_mul,ih,Section5ModMatrix.power]
