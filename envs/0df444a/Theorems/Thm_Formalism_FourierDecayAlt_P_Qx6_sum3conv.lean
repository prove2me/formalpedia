-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sum3conv
-- name    : Formalism.FourierDecayAlt.P.Qx6.sum3conv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:36:12.9798+00:00
-- url     : https://prove2.me/theorems/6bc92868-dfaf-44cf-8a73-d93b397e8498
-- title:
--   Qx6: sum3conv
-- statement:
--   The Qx6 construction uses the sum3conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L402-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L402-L413

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

theorem Formalism.FourierDecayAlt.P.Qx6.sum3conv {M : Type*} [AddCommMonoid M] {t : ℕ} (w : Fin (t + 1)) (F : Fin (t + 1) → Fin (t + 1) → Fin (t + 1) → M) :
    (∑ W, ∑ X, ∑ X', if W ≠ w ∧ X ≠ X' then F W X X' else 0) =
      ∑ w', ∑ x', ∑ x, F (w.succAbove w') (x'.succAbove x) x' := by sorry
