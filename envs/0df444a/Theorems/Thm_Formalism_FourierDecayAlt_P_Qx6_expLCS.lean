-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_expLCS
-- name    : Formalism.FourierDecayAlt.P.Qx6.expLCS
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:33:32.991631+00:00
-- url     : https://prove2.me/theorems/fc3aeae5-5fcd-42ab-be08-a33b255a72d3
-- title:
--   Qx6: exp LCS
-- statement:
--   The Qx6 construction uses the exp LCS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L310-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L310-L320

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
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem Formalism.FourierDecayAlt.P.Qx6.expLCS (hLC : ExpLastCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bS f s) (bS b' c) u =
      ∑ w : Fin t, ((-1 : ℤ) ^ (t + (w : ℕ))) •
        (qminor E (bS f s ∘ w.castSucc.succAbove) b' u * Tm E (u - (t : ℂ)) (f w) c) +
      qminor E f b' u * Tm E (u - (t : ℂ)) s c := by sorry
