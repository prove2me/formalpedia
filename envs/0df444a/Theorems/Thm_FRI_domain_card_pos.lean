-- Prove2me | Theorems.Thm_FRI_domain_card_pos
-- name    : FRI_domain_card_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:59:40.480816+00:00
-- url     : https://prove2.me/theorems/d32a2832-44fa-494c-9aae-ebd34972b064
-- title:
--   FRI domain card pos: FRI domain card pos
-- statement:
--   The FRI domain card pos construction uses the FRI domain card pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L649-L656
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L649-L656

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_domain_card_pos (P : FRIParameters F) (i : Fin (P.num_foldings + 1)) :
    0 < (FRI_domain P i).card := by sorry
