-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_expFCE
-- name    : Formalism.FourierDecayAlt.P.Qx6.expFCE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:33:39.87285+00:00
-- url     : https://prove2.me/theorems/c528be5c-e832-4333-9cdd-6354f646b635
-- title:
--   Qx6: exp FCE
-- statement:
--   The Qx6 construction uses the exp FCE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L293-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L293-L299

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

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

theorem Formalism.FourierDecayAlt.P.Qx6.expFCE (hFC : ExpFirstCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bE s f) (bE c b') u = Tm E u s c * qminor E f b' (u - 1) +
      ∑ w : Fin t, ((-1 : ℤ) ^ ((w : ℕ) + 1)) •
        (Tm E u (f w) c * qminor E (bE s f ∘ w.succ.succAbove) b' (u - 1)) := by sorry
