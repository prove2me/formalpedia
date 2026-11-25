-- Prove2me | Theorems.Thm_DedekindSubgroups_dedekindSum_residue
-- name    : DedekindSubgroups.dedekindSum_residue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:23.422131+00:00
-- url     : https://prove2.me/theorems/f9759e6a-cc39-5c86-be2c-b17c2ffbddf0
-- title:
--   Dedekind Subgroups: dedekind Sum residue
-- statement:
--   The residue form `s(h,k) = k⁻² ∑_r r σ(r) - (k-1)/4`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L202-L226
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L202-L226

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.dedekindSum_residue (hk : 0 < k) (hinv : h * h' % k = 1) :
    dedekindSum h k = (∑ r ∈ range k, (r : ℚ) * sig h k r) / (k : ℚ) ^ 2 - ((k : ℚ) - 1) / 4 := by sorry
