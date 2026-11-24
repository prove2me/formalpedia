-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_w1_commute_of_mem_Glev
-- name    : Formalism.FourierDecayAlt.P.Qx3.w1_commute_of_mem_Glev
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:20:45.819792+00:00
-- url     : https://prove2.me/theorems/29cf280e-219a-4616-935a-5614e07b1ee7
-- title:
--   Qx3: w1 commute of mem Glev
-- statement:
--   The Qx3 construction uses the w1 commute of mem Glev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L673-L710
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L673-L710

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx3.w1_commute_of_mem_Glev (l : Fin r) (c : ℂ) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    w1 k r l c * g = g * w1 k r l c := by sorry
