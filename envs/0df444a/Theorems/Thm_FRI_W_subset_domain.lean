-- Prove2me | Theorems.Thm_FRI_W_subset_domain
-- name    : FRI_W_subset_domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:56:56.347669+00:00
-- url     : https://prove2.me/theorems/6f3d8b83-6a1b-44af-a570-9afded339b2f
-- title:
--   FRI W subset domain: FRI W subset domain
-- statement:
--   The FRI W subset domain construction uses the FRI W subset domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L439-L448
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L439-L448

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W_subset_domain (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (i : ℕ) :
    FRI_W P f_0 T i ⊆ FRI_domain P i := by sorry
