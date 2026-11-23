-- Prove2me | Theorems.Thm_FRI_W0_ratio_le_case_all_large
-- name    : FRI_W0_ratio_le_case_all_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:14:47.744158+00:00
-- url     : https://prove2.me/theorems/2a3dbc94-4f17-42b4-b77d-f9301dfa69d3
-- title:
--   FRI W0 ratio le case all large: FRI W0 ratio le case all large
-- statement:
--   Case 1: When all W_i are large, |W_0|/|D_0| ≤ 1 - δ*.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L574-L614
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L574-L614

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W0_ratio_le_case_all_large
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_pass : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_all_large : ∀ i : Fin (P.num_foldings + 1),
        (FRI_W P f_0 T i).card ≥ (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card)
    (h_no_bad : ∀ i : Fin P.num_foldings,
      ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i)) :
    ((FRI_W P f_0 T 0).card : ℝ) / (FRI_domain P 0).card ≤ 1 - FRI_distance_star P f_0 bound := by sorry
