-- Prove2me | Theorems.Thm_FRI_W_subset_D0
-- name    : FRI_W_subset_D0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:07:24.848794+00:00
-- url     : https://prove2.me/theorems/e372f03a-03ad-4347-a17b-ec0ae7cb0f89
-- title:
--   FRI W subset D0: FRI W subset D0
-- statement:
--   The FRI W subset D0 construction uses the FRI W subset D0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L436-L437
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L436-L437

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W_subset_D0 (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) :
    FRI_W P f_0 T 0 ⊆ P.D_0 := by sorry
