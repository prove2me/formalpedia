-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_sandwich
-- name    : Formalism.FourierDecayAlt.P.Qx6.preserves_sandwich
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:34.933161+00:00
-- url     : https://prove2.me/theorems/88dc2672-2dee-4fa0-a832-7c293b7c400b
-- title:
--   Qx6: preserves sandwich
-- statement:
--   The Qx6 construction uses the preserves sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1196-L1209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1196-L1209

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

theorem Formalism.FourierDecayAlt.P.Qx6.preserves_sandwich {R : Fn k r E → Fn k r E → Prop} (hR : LinRel R) (Y : ℂ) : ∀ (j : ℕ)
    (_ : ∀ l : Fin r, l.val < j → ∀ q, Pres2 R (crd (opL l q)) (crd (opL l q))) {M M' : OM (Fn k r E)}
    (_ : ∀ a b, Pres2 R (M a b) (M' a b)) (a b : Fin 2), Pres2 R (sandw k r Y j M a b) (sandw k r Y j M' a b)
  := by sorry
