-- Prove2me | Theorems.Thm_DedekindSubgroups_sum_inv_eq_sum
-- name    : DedekindSubgroups.sum_inv_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:10:00.848282+00:00
-- url     : https://prove2.me/theorems/72bd2159-6eaf-41bd-bfaf-1471ca5cc575
-- title:
--   Dedekind Subgroups: sum inv eq sum
-- statement:
--   The Dedekind Subgroups construction uses the sum inv eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L154-L162
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L154-L162

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {p : ℕ} [Fact p.Prime]

theorem DedekindSubgroups.sum_inv_eq_sum (H : Subgroup (ZMod p)ˣ) [DecidablePred (· ∈ H)] :
    ∑ u ∈ univ.filter (· ∈ H), ((u⁻¹ : (ZMod p)ˣ) : ZMod p)
      = ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) := by sorry
