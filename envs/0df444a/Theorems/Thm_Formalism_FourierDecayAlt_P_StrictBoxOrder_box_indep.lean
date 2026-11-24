-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_box_indep
-- name    : Formalism.FourierDecayAlt.P.StrictBoxOrder.box_indep
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:52:39.332956+00:00
-- url     : https://prove2.me/theorems/47f434d8-fbc7-4d50-8c30-ceb2aac998fc
-- title:
--   Strict Box Order: box indep
-- statement:
--   The Strict Box Order construction uses the box indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L198-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L198-L205

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StrictBoxOrder
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.StrictBoxOrder.box_indep (hCI : CapIndep) {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (β : ℂ) (L : Fin (n + 1) → ℤ) :
    iSupIndep (fun M : {M : Fin n → ℤ // Box L M} => CapSp E (shf β M.1)) := by sorry
