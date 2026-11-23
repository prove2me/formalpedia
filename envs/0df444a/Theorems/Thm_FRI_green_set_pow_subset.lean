-- Prove2me | Theorems.Thm_FRI_green_set_pow_subset
-- name    : FRI_green_set_pow_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:57:41.174978+00:00
-- url     : https://prove2.me/theorems/df0adf08-2a40-4e1b-846d-128fb8544437
-- title:
--   FRI green set pow subset: FRI green set pow subset
-- statement:
--   The FRI green set pow subset construction uses the FRI green set pow subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L537-L547
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L537-L547

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_green_set_pow_subset {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) (h : i < P.num_foldings) :
    pow_domain (FRI_green_set P f_0 T i) (P.m ⟨i, h⟩) ⊆ FRI_green_set P f_0 T (i + 1) := by sorry
