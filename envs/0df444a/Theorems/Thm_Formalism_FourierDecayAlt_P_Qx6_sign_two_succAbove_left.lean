-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sign_two_succAbove_left
-- name    : Formalism.FourierDecayAlt.P.Qx6.sign_two_succAbove_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:35:43.466388+00:00
-- url     : https://prove2.me/theorems/860b32c8-b8ee-4f95-94ad-f6ecc70aeef3
-- title:
--   Qx6: sign two succ Above left
-- statement:
--   The Qx6 construction uses the sign two succ Above left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L169-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L169-L182

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

theorem Formalism.FourierDecayAlt.P.Qx6.sign_two_succAbove_left {t : ℕ} (b : Fin (t + 1)) (a : Fin t) :
    sg2 (b.succAbove a) b = (-1) ^ ((b : ℕ) + (a : ℕ) + 1) := by sorry
