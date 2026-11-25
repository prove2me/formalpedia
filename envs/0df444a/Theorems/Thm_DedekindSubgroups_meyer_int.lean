-- Prove2me | Theorems.Thm_DedekindSubgroups_meyer_int
-- name    : DedekindSubgroups.meyer_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:27.152885+00:00
-- url     : https://prove2.me/theorems/82cb6abe-b89a-41a6-8781-807ea464b6f3
-- title:
--   Dedekind Subgroups: meyer int
-- statement:
--   Meyer's identity in integer form, valid for every `h`:
--   `k · I(h,k) = ∑_{r<k} (2k - 1 - 3r) σ(r)`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L93-L122
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L93-L122

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.meyer_int (h k : ℕ) (hk : 0 < k) :
    (k : ℤ) * inv h k = ∑ r ∈ range k, (2 * (k : ℤ) - 1 - 3 * r) * sig h k r := by sorry
