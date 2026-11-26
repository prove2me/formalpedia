-- Prove2me | solution 1 for section5_rational_power_operator
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:20.919823+00:00
-- url     : https://prove2.me/submissions/1ce35196-6150-4835-bcaa-78513921ad5f

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
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Computable rational-complex matrix powers and column selection, together with
their exact complex-operator semantics. No eigenvector oracle is used. -/













theorem section5_rational_mul_complex {n : ℕ} (A B : Section5RationalMatrix n) :
    (A.mul B).toComplex=A.toComplex*B.toComplex := by
  ext i j
  simp only [Section5RationalMatrix.mul,Section5RationalMatrix.toComplex,
    Matrix.sub_apply,Matrix.add_apply,Matrix.mul_apply,Rat.cast_sub,Rat.cast_add,Rat.cast_sum,
    Rat.cast_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_mul]
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  rw [Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  linear_combination -(A.im i k:ℂ)*(B.im k j:ℂ)*Complex.I_sq

theorem section5_rational_one_complex (n : ℕ) :
    (Section5RationalMatrix.one n).toComplex=1 := by
  ext i j
  by_cases h : i=j <;>
    simp [Section5RationalMatrix.one,Section5RationalMatrix.toComplex,Matrix.one_apply,h]



theorem section5_rational_mul_operator {n : ℕ} (A B : Section5RationalMatrix n) :
    (A.mul B).operator=A.operator*B.operator := by
  ext x i
  change Matrix.mulVec (A.mul B).toComplex (WithLp.ofLp x) i=
    Matrix.mulVec A.toComplex (Matrix.mulVec B.toComplex (WithLp.ofLp x)) i
  rw [section5_rational_mul_complex,Matrix.mulVec_mulVec]

theorem section5_rational_one_operator (n : ℕ) :
    (Section5RationalMatrix.one n).operator=1 := by
  ext x i
  change Matrix.mulVec (Section5RationalMatrix.one n).toComplex (WithLp.ofLp x) i=x i
  rw [section5_rational_one_complex,Matrix.one_mulVec]























end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (A : Section5RationalMatrix n) (k : ℕ) :
    (A.power k).operator=A.operator^k := by
  induction k with
  | zero => exact section5_rational_one_operator n
  | succ k ih => rw [Section5RationalMatrix.power,section5_rational_mul_operator,ih,pow_succ]
