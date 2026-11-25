-- Prove2me | Theorems.Thm_DedekindSubgroups_one_lt_of_inv
-- name    : DedekindSubgroups.one_lt_of_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:05.580572+00:00
-- url     : https://prove2.me/theorems/fcedcfe8-5fb3-4a39-aa29-010de204b960
-- title:
--   Dedekind Subgroups: one lt of inv
-- statement:
--   The Dedekind Subgroups construction uses the one lt of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L130-L135
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L130-L135

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.one_lt_of_inv (hk : 0 < k) (hinv : h * h' % k = 1) : 1 < k := by sorry
