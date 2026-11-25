-- Prove2me | Theorems.Thm_DedekindSubgroups_card_filter_mem
-- name    : DedekindSubgroups.card_filter_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:57.881702+00:00
-- url     : https://prove2.me/theorems/44d1cc0f-a3ca-5689-944c-6db8aa8ac097
-- title:
--   Dedekind Subgroups: card filter mem
-- statement:
--   The Dedekind Subgroups construction uses the card filter mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L188-L191
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L188-L191

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.card_filter_mem {k : ℕ} [NeZero k] (H : Subgroup (ZMod k)ˣ) [DecidablePred (· ∈ H)] :
    (univ.filter (· ∈ H)).card = Nat.card H := by sorry
