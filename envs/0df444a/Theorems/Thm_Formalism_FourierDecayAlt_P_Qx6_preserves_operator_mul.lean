-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_operator_mul
-- name    : Formalism.FourierDecayAlt.P.Qx6.preserves_operator_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:15.654814+00:00
-- url     : https://prove2.me/theorems/0f4ab8c0-1855-4253-a839-126abd26e71e
-- title:
--   Qx6: preserves operator mul
-- statement:
--   The Qx6 construction uses the preserves operator mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1189-L1194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1189-L1194

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.Qx6.preserves_operator_mul {X : Type*} [AddCommGroup X] [Module ℂ X] {R : X → X → Prop} (hR : LinRel R) {M M' N N' : OM X}
    (hM : ∀ a b, Pres2 R (M a b) (M' a b)) (hN : ∀ a b, Pres2 R (N a b) (N' a b)) (a b : Fin 2) :
    Pres2 R (oMul M N a b) (oMul M' N' a b) := by sorry
