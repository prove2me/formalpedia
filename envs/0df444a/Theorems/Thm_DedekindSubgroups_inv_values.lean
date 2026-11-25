-- Prove2me | Theorems.Thm_DedekindSubgroups_inv_values
-- name    : DedekindSubgroups.inv_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:11:14.984534+00:00
-- url     : https://prove2.me/theorems/05a9f9a6-f322-5de7-a96e-9594acdbace6
-- title:
--   Dedekind Subgroups: inv values
-- statement:
--   The Dedekind Subgroups construction uses the inv values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L50-L51
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean#L50-L51

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
set_option maxRecDepth 100000

theorem DedekindSubgroups.inv_values : inv 4 63 = 720 ∧ inv 16 63 = 720 ∧ inv 22 63 = 882 ∧ inv 43 63 = 882 := by sorry
