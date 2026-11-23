-- Prove2me | Theorems.Thm_FRI_verifier_accepts_iff_s_in_W0
-- name    : FRI_verifier_accepts_iff_s_in_W0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:13:57.401437+00:00
-- url     : https://prove2.me/theorems/fb448bb1-0449-4a58-bc53-8688ef47674d
-- title:
--   FRI verifier accepts iff s in W0: FRI verifier accepts iff s in W0
-- statement:
--   The FRI verifier accepts iff s in W0 construction uses the FRI verifier accepts iff s in W0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L424-L428
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L424-L428

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_verifier_accepts_iff_s_in_W0 (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (h_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings) :
    FRI_verifier_accepts P f_0 T ↔ ∀ j : Fin P.q_rep, (T.s j).val ∈ FRI_W P f_0 T 0 := by sorry
