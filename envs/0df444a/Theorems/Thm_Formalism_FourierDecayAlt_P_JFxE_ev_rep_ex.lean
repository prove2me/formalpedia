-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_rep_ex
-- name    : Formalism.FourierDecayAlt.P.JFxE.ev_rep_ex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:29:21.300548+00:00
-- url     : https://prove2.me/theorems/7d284ff8-e02f-4dcf-ad6e-2c285a4b7819
-- title:
--   JFx E: ev rep ex
-- statement:
--   The JFx E construction uses the ev rep ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L256-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L256-L261

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem Formalism.FourierDecayAlt.P.JFxE.ev_rep_ex {d : ℕ} {a : AA k r E} (ha : Rep d a) :
    ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d) ∧
      ∀ f x, ev Eop a f x = (L.map fun p => p.1 • Fw Eop p.2 f x).sum := by sorry
