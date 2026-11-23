-- Prove2me | Theorems.Thm_FRI_agreement_at_round_zero
-- name    : FRI_agreement_at_round_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:35:37.510358+00:00
-- url     : https://prove2.me/theorems/c58aad5a-0db9-4c33-82a9-12db37a945b5
-- title:
--   FRI agreement at round zero: FRI agreement at round zero
-- statement:
--   The FRI agreement at round zero construction uses the FRI agreement at round zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L405-L419
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L405-L419

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_agreement_at_round_zero (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_large : ∀ i (h : i < P.num_foldings),
        FRI_Is_Large_Subset P f_0 bound i h (FRI_green_set P f_0 T i)) :
    FRI_agreement_at_round P f_0 T 0 := by sorry
