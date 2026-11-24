-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_sk_zero
-- name    : Formalism.FourierDecayAlt.P.JFxE.sk_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:00:37.0627+00:00
-- url     : https://prove2.me/theorems/a43aa3ee-e584-40cb-ba76-b0854ef44c87
-- title:
--   JFx E: sk zero
-- statement:
--   The JFx E construction uses the sk zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L282-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L282-L299

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
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

theorem Formalism.FourierDecayAlt.P.JFxE.sk_zero (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (hb : ¬ Function.Injective b) : ∀ g ∈ GV k r, ev Eop (qminor (Lf k r E) a b u) f g = 0 := by sorry
