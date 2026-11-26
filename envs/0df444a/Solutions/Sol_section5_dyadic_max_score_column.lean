-- Prove2me | solution 1 for section5_dyadic_max_score_column
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:36.46427+00:00
-- url     : https://prove2.me/submissions/b7a2c283-fee1-4a03-b1dd-8cfeb9b68a18

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
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
import Theorems.Thm_section5_integer_power_operator
import Theorems.Thm_section5_rational_column_score
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Exact semantics for the integer circuit's dyadically scaled matrix powers.
Column maximization uses integer sums of squares; no eigenvector or square root
is part of the algorithm. -/

















theorem section5_dyadic_power_operator {n : ℕ} (A : Section5IntegerMatrix n) (q t : ℕ) :
    A.dyadicOperator q^t=((2:ℂ)^(q*t))⁻¹ • (A.power t).operator := by
  rw [Section5IntegerMatrix.dyadicOperator,smul_pow,inv_pow,← pow_mul,
    section5_integer_power_operator]

theorem section5_dyadic_power_column {n : ℕ} (A : Section5IntegerMatrix n)
    (q t : ℕ) (j : Fin n) :
    (A.dyadicOperator q^t) (section5_coordinate_ket j)=
      ((2:ℝ)^(q*t))⁻¹ • (A.power t).operator (section5_coordinate_ket j) := by
  rw [section5_dyadic_power_operator,smul_apply]
  ext i
  simp [Complex.real_smul]



theorem section5_integer_column_score {n : ℕ} (A : Section5IntegerMatrix n) (j : Fin n) :
    ‖A.operator (section5_coordinate_ket j)‖^2=(A.columnScore j:ℝ) := by
  rw [Section5IntegerMatrix.operator,section5_rational_column_score]
  simp [Section5RationalMatrix.columnScore,Section5IntegerMatrix.columnScore,
    Section5IntegerMatrix.toRational]

theorem section5_integer_max_score_column {n : ℕ} (A : Section5IntegerMatrix n)
    (j : Fin n) (hmax : ∀ i, A.columnScore i ≤ A.columnScore j) :
    ∀ i, ‖A.operator (section5_coordinate_ket i)‖ ≤
      ‖A.operator (section5_coordinate_ket j)‖ := by
  intro i
  have hh : (A.columnScore i:ℝ) ≤ (A.columnScore j:ℝ) := by exact_mod_cast hmax i
  rw [← section5_integer_column_score,← section5_integer_column_score] at hh
  nlinarith [norm_nonneg (A.operator (section5_coordinate_ket i)),
    norm_nonneg (A.operator (section5_coordinate_ket j))]















end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (A : Section5IntegerMatrix n)
    (q t : ℕ) (j : Fin n) (hmax : ∀ i, (A.power t).columnScore i ≤ (A.power t).columnScore j) :
    ∀ i, ‖(A.dyadicOperator q^t) (section5_coordinate_ket i)‖ ≤
      ‖(A.dyadicOperator q^t) (section5_coordinate_ket j)‖ := by
  intro i
  rw [section5_dyadic_power_column,section5_dyadic_power_column,norm_smul,norm_smul]
  exact mul_le_mul_of_nonneg_left (section5_integer_max_score_column _ j hmax i) (norm_nonneg _)
