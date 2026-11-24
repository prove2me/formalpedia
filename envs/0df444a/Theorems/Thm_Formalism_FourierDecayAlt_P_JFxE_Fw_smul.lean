-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_smul
-- name    : Formalism.FourierDecayAlt.P.JFxE.Fw_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:28:28.957164+00:00
-- url     : https://prove2.me/theorems/bc498a9d-9eb5-4c58-9bc7-df470110fdf9
-- title:
--   JFx E: Fw smul
-- statement:
--   The JFx E construction uses the Fw smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L181-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L181-L195

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

theorem Formalism.FourierDecayAlt.P.JFxE.Fw_smul (hC : HC Eop) (hL : HL Eop) (hS : HS Eop) : ∀ (w : List (Ix k r)) (c : ℂ) (f : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r, Fw Eop w (fun x => c • f x) g = c • Fw Eop w f g := by sorry
