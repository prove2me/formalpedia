-- Prove2me | Theorems.Thm_FRI_domain_foldable
-- name    : FRI_domain_foldable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:54:09.976923+00:00
-- url     : https://prove2.me/theorems/df9ee399-2ee9-4183-9a15-c2f40c01e85c
-- title:
--   FRI domain foldable: FRI domain foldable
-- statement:
--   The FRI domain foldable construction uses the FRI domain foldable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L512-L516
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L512-L516

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_domain_foldable {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : Fin P.num_foldings) :
    IsFoldable (FRI_domain P i) (P.m i) := by sorry
