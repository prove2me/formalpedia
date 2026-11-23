-- Prove2me | Theorems.Thm_FRI_W_subset_green_set
-- name    : FRI_W_subset_green_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:33:36.825581+00:00
-- url     : https://prove2.me/theorems/600f9859-37d2-4484-84e7-d1380a3d93c4
-- title:
--   FRI W subset green set: FRI W subset green set
-- statement:
--   The FRI W subset green set construction uses the FRI W subset green set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L220-L241
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L220-L241

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W_subset_green_set (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) (h : i ≤ P.num_foldings) :
    FRI_W P f_0 T i ⊆ FRI_green_set P f_0 T i := by sorry
