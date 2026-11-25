-- Prove2me | Theorems.Thm_DedekindSubgroups_sawtooth_mul_div
-- name    : DedekindSubgroups.sawtooth_mul_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:38.887951+00:00
-- url     : https://prove2.me/theorems/ef104798-8bf6-4b59-b9de-5d1f8a586376
-- title:
--   Dedekind Subgroups: sawtooth mul div
-- statement:
--   The Dedekind Subgroups construction uses the sawtooth mul div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L177-L194
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L177-L194

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.sawtooth_mul_div (hinv : h * h' % k = 1) {r : ℕ} (hr0 : 0 < r) (hrk : r < k) :
    sawtooth ((h * r : ℚ) / k) = (sig h k r : ℚ) / k - 1 / 2 := by sorry
