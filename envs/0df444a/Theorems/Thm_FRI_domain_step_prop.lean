-- Prove2me | Theorems.Thm_FRI_domain_step_prop
-- name    : FRI_domain_step_prop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:04:57.55578+00:00
-- url     : https://prove2.me/theorems/a72369b9-2b56-4493-bac0-85bc7e3750d7
-- title:
--   FRI domain step prop: FRI domain step prop
-- statement:
--   If x is in the i-th FRI domain, then x^m_i is in the (i+1)-th domain.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L745-L749
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L745-L749

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_domain_step_prop {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F)
    (i : ℕ) (h : i < P.num_foldings) (x : F) (hx : x ∈ FRI_domain P i) :
    x ^ (P.m ⟨i, h⟩) ∈ FRI_domain P (i + 1) := by sorry
