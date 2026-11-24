-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_oMul_eq
-- name    : Formalism.FourierDecayAlt.P.Qx6.oMul_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:33:44.173822+00:00
-- url     : https://prove2.me/theorems/5e4af062-1829-43f5-a781-a173032f5250
-- title:
--   Qx6: o Mul eq
-- statement:
--   The Qx6 construction uses the o Mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1779-L1781
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1779-L1781

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

theorem Formalism.FourierDecayAlt.P.Qx6.oMul_eq (M N : OM X) (a b : Fin 2) : oMul M N a b = fun f => M a 0 (N 0 b f) + M a 1 (N 1 b f) := by sorry
