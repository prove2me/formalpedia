-- Prove2me | Theorems.Thm_DedekindSubgroups_E_cast
-- name    : DedekindSubgroups.E_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:38.942902+00:00
-- url     : https://prove2.me/theorems/fc9a3b07-69dd-54be-b4f6-4951f1dd5f2e
-- title:
--   Dedekind Subgroups: E cast
-- statement:
--   The Dedekind Subgroups construction uses the E cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L30-L31
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L30-L31

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.E_cast (h k : ℕ) : ((E h k : ℤ) : ℚ) = ∑ r ∈ range k, (r : ℚ) * sig h k r := by sorry
