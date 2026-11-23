-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_isInt_mul_DG
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.isInt_mul_DG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:59.002941+00:00
-- url     : https://prove2.me/theorems/8a61806b-867c-4bcb-a1cd-c8facfffbac5
-- title:
--   Kernel Scaling Back: is Int mul DG
-- statement:
--   The Kernel Scaling Back construction uses the is Int mul DG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L87-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L87-L100

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] {n : ℕ}

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.isInt_mul_DG (R : Subring K) (d : Fin n → Kˣ)
    (hd : ∀ b, ((d b : Kˣ) : K) ∈ R ∧ (((d b)⁻¹ : Kˣ) : K) ∈ R) (Z : Matrix (Fin n) (Fin n) K) :
    IsInt R (Z * ((DG d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ IsInt R Z := by sorry
