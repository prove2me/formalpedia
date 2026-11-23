-- Prove2me | Theorems.Thm_FRI_pow_domain_subset
-- name    : FRI_pow_domain_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:20:54.735806+00:00
-- url     : https://prove2.me/theorems/77fb79de-ff9e-4736-95d4-66096c61ff8f
-- title:
--   FRI pow domain subset: FRI pow domain subset
-- statement:
--   The FRI pow domain subset construction uses the FRI pow domain subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L825-L829
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L825-L829

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_pow_domain_subset {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (h : i < P.num_foldings)
    (S : Finset F) (hS : S ⊆ FRI_domain P i) :
    pow_domain S (P.m ⟨i, h⟩) ⊆ FRI_domain P (i + 1) := by sorry
