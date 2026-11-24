-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_transfer_letter
-- name    : Formalism.FourierDecayAlt.P.Qx6.preserves_transfer_letter
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:24.659029+00:00
-- url     : https://prove2.me/theorems/7da5cc51-a991-4e0a-b199-e29c9a9e0d24
-- title:
--   Qx6: preserves transfer letter
-- statement:
--   The Qx6 construction uses the preserves transfer letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1169-L1177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1169-L1177

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

theorem Formalism.FourierDecayAlt.P.Qx6.preserves_transfer_letter {R : Fn k r E → Fn k r E → Prop} (hR : LinRel R) (l : Fin r)
    (h : ∀ q, Pres2 R (crd (opL l q)) (crd (opL l q))) (Y : ℂ) (a b : Fin 2) :
    Pres2 R (TL k l Y a b) (TL k l Y a b) := by sorry
