-- Prove2me | Theorems.Thm_DedekindSubgroups_sum_pairs_diff
-- name    : DedekindSubgroups.sum_pairs_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:38.58231+00:00
-- url     : https://prove2.me/theorems/87467e15-3758-4198-9a29-5eb28752ccd7
-- title:
--   Dedekind Subgroups: sum pairs diff
-- statement:
--   `∑_{y<m} ∑_{x<y} f (y - x) = ∑_{u<m} (m-u) f u`, assuming `f 0 = 0`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Basic.lean#L57-L73
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Basic.lean#L57-L73

module
public import Mathlib
public import Definitions.Def_DedekindSubgroups_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.sum_pairs_diff (f : ℕ → ℤ) (hf : f 0 = 0) (m : ℕ) :
    ∑ y ∈ range m, ∑ x ∈ range y, f (y - x) = ∑ u ∈ range m, ((m : ℤ) - u) * f u := by sorry
