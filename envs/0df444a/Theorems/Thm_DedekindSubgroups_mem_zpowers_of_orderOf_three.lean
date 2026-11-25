-- Prove2me | Theorems.Thm_DedekindSubgroups_mem_zpowers_of_orderOf_three
-- name    : DedekindSubgroups.mem_zpowers_of_orderOf_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:11:02.139224+00:00
-- url     : https://prove2.me/theorems/823352f5-f45c-5975-90ca-40ca544b8a0e
-- title:
--   Dedekind Subgroups: mem zpowers of order Of three
-- statement:
--   The Dedekind Subgroups construction uses the mem zpowers of order Of three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L37-L47
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L37-L47

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.mem_zpowers_of_orderOf_three {u x : (ZMod 63)ˣ} (hu : orderOf u = 3) :
    x ∈ Subgroup.zpowers u ↔ x ∈ ({1, u, u ^ 2} : Finset (ZMod 63)ˣ) := by sorry
