-- Prove2me | Theorems.Thm_DedekindSubgroups_k_dvd_two_E
-- name    : DedekindSubgroups.k_dvd_two_E
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:18.052349+00:00
-- url     : https://prove2.me/theorems/415b7890-8ed8-4f0c-9b97-ca22b6b2f96b
-- title:
--   Dedekind Subgroups: k dvd two E
-- statement:
--   **Lemma 2.3.** If `3 ∤ k`, then `k ∣ 2 E(h,k)`, hence `2 k s(h,k) ∈ ℤ`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L83-L92
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L83-L92

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.k_dvd_two_E (h3 : ¬ 3 ∣ k) : (k : ℤ) ∣ 2 * E h k := by sorry
