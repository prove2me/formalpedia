-- Prove2me | Theorems.Thm_DedekindSubgroups_orderOf_u22
-- name    : DedekindSubgroups.orderOf_u22
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:11:14.368991+00:00
-- url     : https://prove2.me/theorems/6a389fbc-fb93-421e-9bcc-d8bd9db9fb92
-- title:
--   Dedekind Subgroups: order Of u22
-- statement:
--   The Dedekind Subgroups construction uses the order Of u22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L35-L35
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L35-L35

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.orderOf_u22 : orderOf u22 = 3 := by sorry
