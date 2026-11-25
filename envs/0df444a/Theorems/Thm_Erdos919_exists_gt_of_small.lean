-- Prove2me | Theorems.Thm_Erdos919_exists_gt_of_small
-- name    : Erdos919.exists_gt_of_small
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:13:26.224018+00:00
-- url     : https://prove2.me/theorems/cd7e60ab-76b1-467d-9508-47a9e8923742
-- title:
--   Erdos919: exists gt of small
-- statement:
--   Regularity of `ω₂`: at most `ℵ₁` elements are bounded.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L363-L377
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L363-L377

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section

theorem Erdos919.exists_gt_of_small {J : Type u} (f : J → W.{u}) (hJ : #J ≤ ℵ₁) :
    ∃ u, ∀ j, f j < u := by sorry
