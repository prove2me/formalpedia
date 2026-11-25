-- Prove2me | Theorems.Thm_DedekindSubgroups_sawtooth_div_of_lt
-- name    : DedekindSubgroups.sawtooth_div_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:06.142527+00:00
-- url     : https://prove2.me/theorems/459d5e77-7b96-4286-ac93-0a945b6e6701
-- title:
--   Dedekind Subgroups: sawtooth div of lt
-- statement:
--   The Dedekind Subgroups construction uses the sawtooth div of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L165-L175
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L165-L175

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.sawtooth_div_of_lt {r k : ℕ} (hr0 : 0 < r) (hrk : r < k) :
    sawtooth ((r : ℚ) / k) = (r : ℚ) / k - 1 / 2 := by sorry
