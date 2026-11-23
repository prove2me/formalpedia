-- Prove2me | Theorems.Thm_FRI_induction_step
-- name    : FRI_induction_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:10:05.726508+00:00
-- url     : https://prove2.me/theorems/e21f94c2-5b8f-4afb-ba1a-bcdcd970c1b5
-- title:
--   FRI induction step: FRI induction step
-- statement:
--   The FRI induction step construction uses the FRI induction step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L613-L633
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L613-L633

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_induction_step
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (i : Fin P.num_foldings)
    (h_large : FRI_Is_Large_Subset P f_0 bound i i.isLt (FRI_W P f_0 T i))
    (u_next : FRI_domain P (i + 1) → F)
    (h_u_next_in_code : u_next ∈ FRI_code P (i + 1))
    (h_agree_next : ∀ z ∈ FRI_W P f_0 T (i + 1),
        Fold (FRI_domain P i) (P.m i)
          (extend_by_zero (FRI_domain P i) (FRI_oracle_at_round P f_0 T i i.isLt))
          (T.alpha i) z =
        extend_by_zero (FRI_domain P (i + 1)) u_next z)
    (h_no_bad : ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i)) :
    ∃ u_curr ∈ FRI_code P i, ∀ x ∈ FRI_W P f_0 T i,
        extend_by_zero (FRI_domain P i) (FRI_oracle_at_round P f_0 T i i.isLt) x =
        extend_by_zero (FRI_domain P i) u_curr x := by sorry
