-- Prove2me | Theorems.Thm_DedekindSubgroups_inv_symm
-- name    : DedekindSubgroups.inv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:06:09.455542+00:00
-- url     : https://prove2.me/theorems/31286283-6f82-4158-bd54-35c8af0e5b88
-- title:
--   Dedekind Subgroups: inv symm
-- statement:
--   `I(h⁻¹, k) = I(h, k)`: `(x, y) ↦ (σ(y), σ(x))` maps inversions of `σ_h` onto those of `σ_{h⁻¹}`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L49-L71
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L49-L71

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity
set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.inv_symm (hk : 0 < k) (hinv : h * h' % k = 1) : inv h' k = inv h k := by sorry
