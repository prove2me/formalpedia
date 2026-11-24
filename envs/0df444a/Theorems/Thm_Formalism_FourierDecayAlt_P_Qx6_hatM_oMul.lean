-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_hatM_oMul
-- name    : Formalism.FourierDecayAlt.P.Qx6.hatM_oMul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:35:59.084809+00:00
-- url     : https://prove2.me/theorems/7a69dd30-1ac5-4fc7-8aa9-2b6abbab1a27
-- title:
--   Qx6: hat M o Mul
-- statement:
--   The Qx6 construction uses the hat M o Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1788-L1794
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1788-L1794

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
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (H : HatData X)
variable {H}

theorem Formalism.FourierDecayAlt.P.Qx6.hatM_oMul {M N : OM X} (hM : ∀ a b, H.Good (M a b)) (hN : ∀ a b, H.Good (N a b)) :
    hatM H (oMul M N) = hatM H M * hatM H N := by sorry
