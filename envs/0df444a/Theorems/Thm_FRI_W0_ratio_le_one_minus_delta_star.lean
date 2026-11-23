-- Prove2me | Theorems.Thm_FRI_W0_ratio_le_one_minus_delta_star
-- name    : FRI_W0_ratio_le_one_minus_delta_star
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:14:51.929625+00:00
-- url     : https://prove2.me/theorems/87eec165-d9e4-4a9a-8702-b8e1f8ee87ed
-- title:
--   FRI W0 ratio le one minus delta star: FRI W0 ratio le one minus delta star
-- statement:
--   The FRI W0 ratio le one minus delta star construction uses the FRI W0 ratio le one minus delta star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L624-L640
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L624-L640

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W0_ratio_le_one_minus_delta_star
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_pass : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_domain_size : FRI_Domain_Size_Property P)
    (h_D_pos : ∀ i : Fin (P.num_foldings + 1), (FRI_domain P i).card > 0) :
    ((FRI_W P f_0 T 0).card : ℝ) / (FRI_domain P 0).card ≤ 1 - FRI_distance_star P f_0 bound := by sorry
