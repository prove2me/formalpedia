-- Prove2me | solution 1 for section5_rational_column_score
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:57.566744+00:00
-- url     : https://prove2.me/submissions/5fb2799f-40a7-45e6-a006-ad82211af141

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
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (A : Section5RationalMatrix n) (j : Fin n) :
    ‖A.operator (section5_coordinate_ket j)‖^2=(A.columnScore j:ℝ) := by
  have hc : A.operator (section5_coordinate_ket j)=WithLp.toLp 2 (fun i => A.toComplex i j) := by
    ext i
    change Matrix.mulVec A.toComplex (Pi.single j (1:ℂ)) i=A.toComplex i j
    rw [Matrix.mulVec_single]
    simp
  rw [hc,EuclideanSpace.norm_sq_eq]
  simp only [Section5RationalMatrix.columnScore,Rat.cast_sum,Rat.cast_add,Rat.cast_pow,
    WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [Section5RationalMatrix.toComplex,pow_two]
