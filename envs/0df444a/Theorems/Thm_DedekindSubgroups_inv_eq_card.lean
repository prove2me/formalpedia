-- Prove2me | Theorems.Thm_DedekindSubgroups_inv_eq_card
-- name    : DedekindSubgroups.inv_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:05:42.113583+00:00
-- url     : https://prove2.me/theorems/e9762c14-7b65-41cb-b00e-e4a1c383daff
-- title:
--   Dedekind Subgroups: inv eq card
-- statement:
--   The Dedekind Subgroups construction uses the inv eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L33-L46
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L33-L46

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity
set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.inv_eq_card (h k : ℕ) : inv h k = (invSet h k).card := by sorry
