-- Prove2me | Theorems.Thm_DedekindSubgroups_subgroupSum_eq_of_mem_iff
-- name    : DedekindSubgroups.subgroupSum_eq_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:10:51.552569+00:00
-- url     : https://prove2.me/theorems/86388ce7-4003-5196-9294-eafb6df3264d
-- title:
--   Dedekind Subgroups: subgroup Sum eq of mem iff
-- statement:
--   The Dedekind Subgroups construction uses the subgroup Sum eq of mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L16-L23
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L16-L23

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.subgroupSum_eq_of_mem_iff {k : ℕ} [NeZero k] (H : Subgroup (ZMod k)ˣ)
    (t : Finset (ZMod k)ˣ) (ht : ∀ x, x ∈ H ↔ x ∈ t) :
    subgroupSum H = ∑ u ∈ t, dedekindSum (u : ZMod k).val k := by sorry
