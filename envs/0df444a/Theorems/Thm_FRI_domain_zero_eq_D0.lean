-- Prove2me | Theorems.Thm_FRI_domain_zero_eq_D0
-- name    : FRI_domain_zero_eq_D0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:57:09.98074+00:00
-- url     : https://prove2.me/theorems/c8e22ab9-ec0a-401e-8d30-a0fe5121b731
-- title:
--   FRI domain zero eq D0: FRI domain zero eq D0
-- statement:
--   The FRI domain zero eq D0 construction uses the FRI domain zero eq D0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L309-L309
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L309-L309

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_domain_zero_eq_D0 (P : FRIParameters F) : FRI_domain P 0 = P.D_0 := by sorry
