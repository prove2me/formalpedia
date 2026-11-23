-- Prove2me | Theorems.Thm_FRI_State_step
-- name    : FRI_State_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:07:13.469648+00:00
-- url     : https://prove2.me/theorems/05999071-7daf-4e60-87db-5e495f759bd7
-- title:
--   FRI State step: FRI State step
-- statement:
--   The FRI State step construction uses the FRI State step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L152-L157
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L152-L157

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_State_step (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i : ℕ) (h : i < P.num_foldings) :
    FRI_State P f_0 bound T (i + 1) ↔
    FRI_State P f_0 bound T i ∨
      FRI_BadEvent P f_0 bound ⟨i, h⟩ (FRI_oracle_at_round P f_0 T i h) (T.alpha ⟨i, h⟩) := by sorry
