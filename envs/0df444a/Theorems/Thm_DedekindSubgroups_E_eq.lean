-- Prove2me | Theorems.Thm_DedekindSubgroups_E_eq
-- name    : DedekindSubgroups.E_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:05.839108+00:00
-- url     : https://prove2.me/theorems/abda1539-3a0f-47bc-9864-49d68cfa921d
-- title:
--   Dedekind Subgroups: E eq
-- statement:
--   `E(h,k) = h ∑ r² - k ∑ r q_r`, where `q_r = ⌊h r / k⌋`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L43-L48
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L43-L48

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.E_eq (h k : ℕ) :
    E h k = h * ∑ r ∈ range k, (r : ℤ) ^ 2 - k * ∑ r ∈ range k, (r : ℤ) * ((h * r / k : ℕ) : ℤ) := by sorry
