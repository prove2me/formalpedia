-- Prove2me | Theorems.Thm_DedekindSubgroups_six_mul_sum_sq
-- name    : DedekindSubgroups.six_mul_sum_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:41.5003+00:00
-- url     : https://prove2.me/theorems/45eaaa90-b24f-53d2-88bc-5d67d783ab91
-- title:
--   Dedekind Subgroups: six mul sum sq
-- statement:
--   `6 ∑_{r<m} r² = m (m-1) (2m-1)`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L21-L25
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L21-L25

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.six_mul_sum_sq (m : ℕ) :
    6 * ∑ r ∈ range m, (r : ℤ) ^ 2 = (m : ℤ) * (m - 1) * (2 * m - 1) := by sorry
