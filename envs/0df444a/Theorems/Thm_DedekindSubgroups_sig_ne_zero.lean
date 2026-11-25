-- Prove2me | Theorems.Thm_DedekindSubgroups_sig_ne_zero
-- name    : DedekindSubgroups.sig_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:31.244372+00:00
-- url     : https://prove2.me/theorems/eba4ecd4-2b20-48cc-a630-f7871fcd404c
-- title:
--   Dedekind Subgroups: sig ne zero
-- statement:
--   The Dedekind Subgroups construction uses the sig ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L155-L163
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L155-L163

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.sig_ne_zero (hinv : h * h' % k = 1) {r : ℕ} (hr0 : 0 < r) (hrk : r < k) :
    sig h k r ≠ 0 := by sorry
