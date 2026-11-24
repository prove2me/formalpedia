-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_expFCS
-- name    : Formalism.FourierDecayAlt.P.Qx6.expFCS
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:37:30.863285+00:00
-- url     : https://prove2.me/theorems/2ee721a8-5a46-4b0e-83c3-b9e170460c8a
-- title:
--   Qx6: exp FCS
-- statement:
--   The Qx6 construction uses the exp FCS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L301-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L301-L308

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

theorem Formalism.FourierDecayAlt.P.Qx6.expFCS (hFC : ExpFirstCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bS f s) (bE c b') u =
      ∑ w : Fin t, ((-1 : ℤ) ^ (w : ℕ)) •
        (Tm E u (f w) c * qminor E (bS f s ∘ w.castSucc.succAbove) b' (u - 1)) +
      ((-1 : ℤ) ^ t) • (Tm E u s c * qminor E f b' (u - 1)) := by sorry
