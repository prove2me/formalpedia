-- Prove2me | Theorems.Thm_DedekindSubgroups_orderOf_u4
-- name    : DedekindSubgroups.orderOf_u4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:11:25.75148+00:00
-- url     : https://prove2.me/theorems/4dc385f0-23ae-45a4-8a21-8f01cb4b7474
-- title:
--   Dedekind Subgroups: order Of u4
-- statement:
--   The Dedekind Subgroups construction uses the order Of u4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L33-L33
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L33-L33

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.orderOf_u4 : orderOf u4 = 3 := by sorry
