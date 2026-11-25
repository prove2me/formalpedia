-- Prove2me | Theorems.Thm_DedekindSubgroups_sum_range_cast_id
-- name    : DedekindSubgroups.sum_range_cast_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:10.972178+00:00
-- url     : https://prove2.me/theorems/269275bf-496b-4edf-8b79-e111a335b94b
-- title:
--   Dedekind Subgroups: sum range cast id
-- statement:
--   The Dedekind Subgroups construction uses the sum range cast id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L196-L199
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L196-L199

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.sum_range_cast_id (k : ℕ) : (∑ r ∈ range k, (r : ℚ)) = (k : ℚ) * (k - 1) / 2 := by sorry
