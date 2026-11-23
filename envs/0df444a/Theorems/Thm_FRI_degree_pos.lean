-- Prove2me | Theorems.Thm_FRI_degree_pos
-- name    : FRI_degree_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:10:49.53931+00:00
-- url     : https://prove2.me/theorems/a7cab6fe-bb65-49a6-83e8-bad2362228cf
-- title:
--   FRI degree pos: FRI degree pos
-- statement:
--   The FRI degree pos construction uses the FRI degree pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L725-L732
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L725-L732

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_degree_pos (P : FRIParameters F) (i : ℕ) (hi : i ≤ P.num_foldings) :
    0 < FRI_degree P i := by sorry
