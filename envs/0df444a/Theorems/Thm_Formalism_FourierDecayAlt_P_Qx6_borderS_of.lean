-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_borderS_of
-- name    : Formalism.FourierDecayAlt.P.Qx6.borderS_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:37:09.243435+00:00
-- url     : https://prove2.me/theorems/dfa1f9c5-a861-4899-820b-e78c4ab6fb18
-- title:
--   Qx6: border S of
-- statement:
--   The Qx6 construction uses the border S of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L370-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L370-L382

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

theorem Formalism.FourierDecayAlt.P.Qx6.borderS_of (hLC : ExpLastCol) (hFR : ExpFirstRow) (hSk : QSkewRow) : BorderS := by sorry
