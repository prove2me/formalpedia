-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_add
-- name    : Formalism.FourierDecayAlt.P.JFxE.Fw_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:29:02.750838+00:00
-- url     : https://prove2.me/theorems/d7c5c0c6-8d9d-4664-aaa7-5fef725aecf3
-- title:
--   JFx E: Fw add
-- statement:
--   The JFx E construction uses the Fw add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L159-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L159-L179

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

theorem Formalism.FourierDecayAlt.P.JFxE.Fw_add (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) : ∀ (w : List (Ix k r)) (f f₂ : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂ →
    ∀ g ∈ GV k r, Fw Eop w (fun x => f x + f₂ x) g = Fw Eop w f g + Fw Eop w f₂ g := by sorry
