-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sum_ne_succAbove
-- name    : Formalism.FourierDecayAlt.P.Qx6.sum_ne_succAbove
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:35:00.552606+00:00
-- url     : https://prove2.me/theorems/7e42bb41-7b4a-4221-b159-ba531145c976
-- title:
--   Qx6: sum ne succ Above
-- statement:
--   The Qx6 construction uses the sum ne succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L397-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L397-L400

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

theorem Formalism.FourierDecayAlt.P.Qx6.sum_ne_succAbove {M : Type*} [AddCommMonoid M] {t : ℕ} (p : Fin (t + 1)) (f : Fin (t + 1) → M) :
    (∑ W, if W ≠ p then f W else 0) = ∑ w, f (p.succAbove w) := by sorry
