-- Prove2me | Theorems.Thm_DedekindSubgroups_meyer
-- name    : DedekindSubgroups.meyer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:05:07.177908+00:00
-- url     : https://prove2.me/theorems/52745315-b08d-4e19-bb87-99681c325f0e
-- title:
--   Dedekind Subgroups: meyer
-- statement:
--   **Meyer's formula**: `12 k s(h,k) = (k-1)(k-2) - 4 I(h,k)`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L229-L244
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L229-L244

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.meyer (hk : 0 < k) (hinv : h * h' % k = 1) :
    12 * (k : ℚ) * dedekindSum h k = ((k : ℚ) - 1) * ((k : ℚ) - 2) - 4 * inv h k := by sorry
