-- Prove2me | Theorems.Thm_FRI_W_eq_image
-- name    : FRI_W_eq_image
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:09:46.488433+00:00
-- url     : https://prove2.me/theorems/70784d1d-e306-42cd-b829-b5189acc7cbd
-- title:
--   FRI W eq image: FRI W eq image
-- statement:
--   The FRI W eq image construction uses the FRI W eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L499-L507
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L499-L507

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W_eq_image (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) (h : i ≤ P.num_foldings) :
    FRI_W P f_0 T i = (FRI_W P f_0 T 0).image (fun s ↦ folded_query P s i) := by sorry
