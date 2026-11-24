-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_isWt_mono
-- name    : Formalism.FourierDecayAlt.P.StrictBoxOrder.isWt_mono
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:53:08.286443+00:00
-- url     : https://prove2.me/theorems/42bf1bc0-db54-4362-94b4-72244dd3e6fd
-- title:
--   Strict Box Order: is Wt mono
-- statement:
--   The Strict Box Order construction uses the is Wt mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L71-L77

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

theorem Formalism.FourierDecayAlt.P.StrictBoxOrder.isWt_mono {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {y : Fin n → Module.End ℂ V} (hy : IsVec E y)
    (a : Fin n → ℕ) (v : V) (h : IsWt E v) : IsWt E (mono y a v) := by sorry
