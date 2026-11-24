-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sign_pair_succAbove_right
-- name    : Formalism.FourierDecayAlt.P.Qx6.sign_pair_succAbove_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:34:29.261993+00:00
-- url     : https://prove2.me/theorems/6679b453-313a-4ff2-ac9a-ec5a678d3f4e
-- title:
--   Qx6: sign pair succ Above right
-- statement:
--   The Qx6 construction uses the sign pair succ Above right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L155-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L155-L167

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

theorem Formalism.FourierDecayAlt.P.Qx6.sign_pair_succAbove_right {t : ℕ} (b : Fin (t + 1)) (a : Fin t) :
    sg2 b (b.succAbove a) = (-1) ^ ((b : ℕ) + (a : ℕ)) := by sorry
