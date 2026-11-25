-- Prove2me | Theorems.Thm_DedekindSubgroups_sum_pairs_left
-- name    : DedekindSubgroups.sum_pairs_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:33.945299+00:00
-- url     : https://prove2.me/theorems/24d82d09-d9dc-4e2b-9707-f8059585e15d
-- title:
--   Dedekind Subgroups: sum pairs left
-- statement:
--   `∑_{y<m} ∑_{x<y} f x = ∑_{x<m} (m-1-x) f x`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Basic.lean#L36-L47
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Basic.lean#L36-L47

module
public import Mathlib
public import Definitions.Def_DedekindSubgroups_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.sum_pairs_left (f : ℕ → ℤ) (m : ℕ) :
    ∑ y ∈ range m, ∑ x ∈ range y, f x = ∑ x ∈ range m, ((m : ℤ) - 1 - x) * f x := by sorry
