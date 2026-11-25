-- Prove2me | Theorems.Thm_DedekindSubgroups_sum_pairs_right
-- name    : DedekindSubgroups.sum_pairs_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:33.123838+00:00
-- url     : https://prove2.me/theorems/a605d5da-07a1-5da5-a7f4-88109bcfce49
-- title:
--   Dedekind Subgroups: sum pairs right
-- statement:
--   `∑_{y<m} ∑_{x<y} g y = ∑_{y<m} y g y`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Basic.lean#L50-L54
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Basic.lean#L50-L54

module
public import Mathlib
public import Definitions.Def_DedekindSubgroups_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.sum_pairs_right (g : ℕ → ℤ) (m : ℕ) :
    ∑ y ∈ range m, ∑ _x ∈ range y, g y = ∑ y ∈ range m, (y : ℤ) * g y := by sorry
