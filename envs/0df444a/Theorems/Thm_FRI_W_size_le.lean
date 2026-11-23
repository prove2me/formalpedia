-- Prove2me | Theorems.Thm_FRI_W_size_le
-- name    : FRI_W_size_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:09:44.083335+00:00
-- url     : https://prove2.me/theorems/77f238ee-08e5-4136-a317-70adce41579a
-- title:
--   FRI W size le: FRI W size le
-- statement:
--   The FRI W size le construction uses the FRI W size le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L454-L476
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L454-L476

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W_size_le (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) (h : i < P.num_foldings) :
    (FRI_W P f_0 T i).card ≤ P.m ⟨i, h⟩ * (FRI_W P f_0 T (i + 1)).card := by sorry
