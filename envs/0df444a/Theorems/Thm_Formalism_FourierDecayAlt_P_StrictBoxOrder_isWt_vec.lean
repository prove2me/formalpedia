-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_isWt_vec
-- name    : Formalism.FourierDecayAlt.P.StrictBoxOrder.isWt_vec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:53:35.00715+00:00
-- url     : https://prove2.me/theorems/e3fc01b9-732a-4fa2-87a1-72eb94277936
-- title:
--   Strict Box Order: is Wt vec
-- statement:
--   The Strict Box Order construction uses the is Wt vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L38-L51

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

theorem Formalism.FourierDecayAlt.P.StrictBoxOrder.isWt_vec {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {y : Fin n → Module.End ℂ V} (hy : IsVec E y)
    (x : Fin n) (v : V) (h : IsWt E v) : IsWt E (y x v) := by sorry
