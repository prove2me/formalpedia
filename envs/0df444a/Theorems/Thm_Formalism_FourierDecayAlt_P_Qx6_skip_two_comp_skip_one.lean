-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_skip_two_comp_skip_one
-- name    : Formalism.FourierDecayAlt.P.Qx6.skip_two_comp_skip_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:34:52.738581+00:00
-- url     : https://prove2.me/theorems/3179069a-e525-4e27-a2a1-dcb4fa681d74
-- title:
--   Qx6: skip two comp skip one
-- statement:
--   The Qx6 construction uses the skip two comp skip one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L415-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L415-L426

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

theorem Formalism.FourierDecayAlt.P.Qx6.skip_two_comp_skip_one {n : ℕ} : ∀ {t : ℕ} (v : Fin (t + 1) → Fin n) (w : Fin (t + 1)) (w' : Fin t),
    (v ∘ skip2 (min (w.succAbove w') w) (max (w.succAbove w') w) : Fin (t + 1 - 2) → Fin n) =
      (v ∘ w.succAbove) ∘ skip1 w'
  := by sorry
