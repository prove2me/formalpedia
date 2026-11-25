-- Prove2me | Theorems.Thm_DedekindSubgroups_sig_eq_sub
-- name    : DedekindSubgroups.sig_eq_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:08.30421+00:00
-- url     : https://prove2.me/theorems/ed2c55cd-3a25-4500-aab1-68d342537933
-- title:
--   Dedekind Subgroups: sig eq sub
-- statement:
--   `σ_h(r) = h r - k ⌊h r / k⌋`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L34-L40
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L34-L40

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.sig_eq_sub (h k r : ℕ) :
    (sig h k r : ℤ) = h * r - k * ((h * r / k : ℕ) : ℤ) := by sorry
