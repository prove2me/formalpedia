-- Prove2me | Theorems.Thm_FRI_W_ratio_le
-- name    : FRI_W_ratio_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:59:24.423662+00:00
-- url     : https://prove2.me/theorems/a8e8848c-7368-4eba-9ccc-0b36fe9add56
-- title:
--   FRI W ratio le: FRI W ratio le
-- statement:
--   The FRI W ratio le construction uses the FRI W ratio le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L478-L497
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L478-L497

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W_ratio_le (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (h_domain_size : FRI_Domain_Size_Property P)
    (i : ℕ) (h : i < P.num_foldings) :
    ((FRI_W P f_0 T i).card : ℝ) / (FRI_domain P i).card ≤
      ((FRI_W P f_0 T (i + 1)).card : ℝ) / (FRI_domain P (i + 1)).card := by sorry
