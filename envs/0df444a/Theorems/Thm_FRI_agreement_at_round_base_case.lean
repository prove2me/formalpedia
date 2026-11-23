-- Prove2me | Theorems.Thm_FRI_agreement_at_round_base_case
-- name    : FRI_agreement_at_round_base_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:13:48.76296+00:00
-- url     : https://prove2.me/theorems/b4c41a29-db87-4e90-b918-85c2598e3ff3
-- title:
--   FRI agreement at round base case: FRI agreement at round base case
-- statement:
--   The FRI agreement at round base case construction uses the FRI agreement at round base case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L371-L389
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L371-L389

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_agreement_at_round_base_case (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (h_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings) :
    FRI_agreement_at_round P f_0 T (Fin.last P.num_foldings) := by sorry
