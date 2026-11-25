-- Prove2me | Theorems.Thm_DedekindSubgroups_two_mul_dedekindSum_int
-- name    : DedekindSubgroups.two_mul_dedekindSum_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:51.613125+00:00
-- url     : https://prove2.me/theorems/f39e784b-455b-4762-bb69-d3f456872f3b
-- title:
--   Dedekind Subgroups: two mul dedekind Sum int
-- statement:
--   The Dedekind Subgroups construction uses the two mul dedekind Sum int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L94-L107
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L94-L107

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.two_mul_dedekindSum_int (hk : 0 < k) (hinv : h * h' % k = 1) (h3 : ¬ 3 ∣ k) :
    ∃ c : ℤ, (c : ℚ) = 2 * k * dedekindSum h k := by sorry
