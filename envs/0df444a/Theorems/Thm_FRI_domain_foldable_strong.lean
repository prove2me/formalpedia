-- Prove2me | Theorems.Thm_FRI_domain_foldable_strong
-- name    : FRI_domain_foldable_strong
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:03:44.699796+00:00
-- url     : https://prove2.me/theorems/b93fe9fe-a3b3-453d-9531-4ac12dd1427a
-- title:
--   FRI domain foldable strong: FRI domain foldable strong
-- statement:
--   Strengthened foldability: FRI_domain P i is foldable with prod_tail
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L490-L501
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L490-L501

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_domain_foldable_strong {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (hi : i ≤ P.num_foldings) :
    IsFoldable (FRI_domain P i) (FRI_prod_tail P i) := by sorry
