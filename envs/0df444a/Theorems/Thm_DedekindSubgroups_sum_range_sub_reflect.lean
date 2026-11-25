-- Prove2me | Theorems.Thm_DedekindSubgroups_sum_range_sub_reflect
-- name    : DedekindSubgroups.sum_range_sub_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:31.3788+00:00
-- url     : https://prove2.me/theorems/378818b7-c4c4-439c-8b22-749c47940e01
-- title:
--   Dedekind Subgroups: sum range sub reflect
-- statement:
--   `∑_{x<y} f (y - x) = ∑_{j<y} f (j + 1)`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Basic.lean#L26-L33
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Basic.lean#L26-L33

module
public import Mathlib
public import Definitions.Def_DedekindSubgroups_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.sum_range_sub_reflect (f : ℕ → ℤ) (y : ℕ) :
    ∑ x ∈ range y, f (y - x) = ∑ j ∈ range y, f (j + 1) := by sorry
