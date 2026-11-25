-- Prove2me | Theorems.Thm_DedekindSubgroups_sum_subgroup_eq_zero
-- name    : DedekindSubgroups.sum_subgroup_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:10:00.843932+00:00
-- url     : https://prove2.me/theorems/4c439072-2e2f-4a82-ab7c-231d4c2189b7
-- title:
--   Dedekind Subgroups: sum subgroup eq zero
-- statement:
--   For a nontrivial subgroup `H`, `∑_{h ∈ H} h ≡ 0 (mod p)`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L165-L182
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L165-L182

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {p : ℕ} [Fact p.Prime]

theorem DedekindSubgroups.sum_subgroup_eq_zero (H : Subgroup (ZMod p)ˣ) [DecidablePred (· ∈ H)] (hH : H ≠ ⊥) :
    ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) = 0 := by sorry
