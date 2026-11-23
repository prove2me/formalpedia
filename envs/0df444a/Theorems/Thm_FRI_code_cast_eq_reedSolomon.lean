-- Prove2me | Theorems.Thm_FRI_code_cast_eq_reedSolomon
-- name    : FRI_code_cast_eq_reedSolomon
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:24:54.873413+00:00
-- url     : https://prove2.me/theorems/d452ee5e-288b-45c2-83f3-dbf41438eb56
-- title:
--   FRI code cast eq reed Solomon: FRI code cast eq reed Solomon
-- statement:
--   The FRI code cast eq reed Solomon construction uses the FRI code cast eq reed Solomon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L275-L286
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L275-L286

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_code_cast_eq_reedSolomon {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (h : i < P.num_foldings) :
    FRI_code_cast P i h =
      reedSolomon (pow_domain (FRI_domain P i) (P.m ⟨i, h⟩)) (FRI_degree P (i + 1)) := by sorry
