-- Prove2me | Theorems.Thm_FRI_degree_succ_eq
-- name    : FRI_degree_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:54:07.32953+00:00
-- url     : https://prove2.me/theorems/76f75897-9e73-4984-80de-0cf21b953f37
-- title:
--   FRI degree succ eq: FRI degree succ eq
-- statement:
--   Helper lemma: d_{i+1} = d_i / m_{i+1}
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L758-L761
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L758-L761

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_degree_succ_eq {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (h : i < P.num_foldings) :
    FRI_degree P (i + 1) = FRI_degree P i / P.m ⟨i, h⟩ := by sorry
