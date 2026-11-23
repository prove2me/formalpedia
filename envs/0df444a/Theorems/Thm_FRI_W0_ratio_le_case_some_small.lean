-- Prove2me | Theorems.Thm_FRI_W0_ratio_le_case_some_small
-- name    : FRI_W0_ratio_le_case_some_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:14:35.519167+00:00
-- url     : https://prove2.me/theorems/0fe8724e-6338-4e99-a030-1ccf7b78f3d3
-- title:
--   FRI W0 ratio le case some small: FRI W0 ratio le case some small
-- statement:
--   Case 2: When some W_i is small, |W_0|/|D_0| ≤ 1 - δ*.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L561-L571
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L561-L571

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W0_ratio_le_case_some_small
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_domain_size : FRI_Domain_Size_Property P)
    (h_D_pos : ∀ i : Fin (P.num_foldings + 1), (FRI_domain P i).card > 0)
    (i_star : Fin (P.num_foldings + 1))
    (h_small : (FRI_W P f_0 T i_star).card <
      (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i_star).card) :
    ((FRI_W P f_0 T 0).card : ℝ) / (FRI_domain P 0).card ≤ 1 - FRI_distance_star P f_0 bound := by sorry
