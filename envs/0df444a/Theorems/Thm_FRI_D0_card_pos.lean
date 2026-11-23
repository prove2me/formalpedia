-- Prove2me | Theorems.Thm_FRI_D0_card_pos
-- name    : FRI_D0_card_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:56:59.345239+00:00
-- url     : https://prove2.me/theorems/badeb899-34dd-423d-91b7-b194fcffdf5d
-- title:
--   FRI D0 card pos: FRI D0 card pos
-- statement:
--   The FRI D0 card pos construction uses the FRI D0 card pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L302-L304
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L302-L304

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_D0_card_pos {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) :
    0 < (FRI_domain P 0).card := by sorry
