-- Prove2me | Theorems.Thm_FRI_State_independent_of_s
-- name    : FRI_State_independent_of_s
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:00:55.628733+00:00
-- url     : https://prove2.me/theorems/135ff025-9410-4f81-b13c-edc1ae2eccff
-- title:
--   FRI State independent of s: FRI State independent of s
-- statement:
--   The FRI State independent of s construction uses the FRI State independent of s property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L475-L489
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L475-L489

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_State_independent_of_s (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (f : (i : Fin P.num_foldings) → FRI_domain P i.val.succ → F)
    (alpha : Fin P.num_foldings → F)
    (s1 s2 : Fin P.q_rep → P.D_0)
    (i : ℕ) (h : i ≤ P.num_foldings) :
    FRI_State P f_0 bound { f := f, alpha := alpha, s := s1 } i ↔
    FRI_State P f_0 bound { f := f, alpha := alpha, s := s2 } i := by sorry
