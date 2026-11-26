-- Prove2me | solution 1 for section5_integer_power_operator
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:33.154819+00:00
-- url     : https://prove2.me/submissions/b2651c33-1252-4fbe-8778-1d19e196daf2

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
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
import Theorems.Thm_section5_rational_power_operator
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Exact semantics for the integer circuit's dyadically scaled matrix powers.
Column maximization uses integer sums of squares; no eigenvector or square root
is part of the algorithm. -/

@[ext] theorem Section5RationalMatrix.ext {n : ℕ} {A B : Section5RationalMatrix n}
    (hre : A.re=B.re) (him : A.im=B.im) : A=B := by
  cases A
  cases B
  cases hre
  cases him
  rfl



theorem section5_integer_to_rational_mul {n : ℕ} (A B : Section5IntegerMatrix n) :
    (A.mul B).toRational=A.toRational.mul B.toRational := by
  apply Section5RationalMatrix.ext <;> funext i j <;>
    simp [Section5IntegerMatrix.toRational,Section5IntegerMatrix.mul,
      Section5RationalMatrix.mul,Matrix.mul_apply] <;> rfl

theorem section5_integer_to_rational_one (n : ℕ) :
    (Section5IntegerMatrix.one n).toRational=Section5RationalMatrix.one n := by
  apply Section5RationalMatrix.ext <;> funext i j <;>
    by_cases h : i=j <;>
    simp [Section5IntegerMatrix.toRational,Section5IntegerMatrix.one,
      Section5RationalMatrix.one,Matrix.one_apply,h]

theorem section5_integer_to_rational_power {n : ℕ} (A : Section5IntegerMatrix n) (t : ℕ) :
    (A.power t).toRational=A.toRational.power t := by
  induction t with
  | zero => exact section5_integer_to_rational_one n
  | succ t ih =>
    rw [Section5IntegerMatrix.power,section5_integer_to_rational_mul,ih,
      Section5RationalMatrix.power]































end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (A : Section5IntegerMatrix n) (t : ℕ) :
    (A.power t).operator=A.operator^t := by
  change (A.power t).toRational.operator=A.toRational.operator^t
  rw [section5_integer_to_rational_power,section5_rational_power_operator]
