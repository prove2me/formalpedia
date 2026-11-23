-- Prove2me | Theorems.Thm_FRI_State_monotone
-- name    : FRI_State_monotone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:07:12.126204+00:00
-- url     : https://prove2.me/theorems/3a0e33bf-5532-4819-a67f-42dacd957ae2
-- title:
--   FRI State monotone: FRI State monotone
-- statement:
--   The FRI State monotone construction uses the FRI State monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L159-L173
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L159-L173

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_State_monotone (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i j : ℕ) (h : i ≤ j) :
    FRI_State P f_0 bound T i → FRI_State P f_0 bound T j := by sorry
