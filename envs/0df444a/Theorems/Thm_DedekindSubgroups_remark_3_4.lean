-- Prove2me | Theorems.Thm_DedekindSubgroups_remark_3_4
-- name    : DedekindSubgroups.remark_3_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:14:45.936955+00:00
-- url     : https://prove2.me/theorems/52e7800a-f4be-5818-b454-e45964281d64
-- title:
--   Dedekind Subgroups: remark 3 4
-- statement:
--   **Remark 3.4.** For every subgroup `H` of `(ℤ/kℤ)ˣ`, `12 k S(H,k)` is an integer congruent to
--   `|H|(k-1)(k-2) - 4 ∑_{h ∈ H, h² = 1} I(h,k)` modulo `8`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/Solution.lean#L35-L40
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/Solution.lean#L35-L40

module
public import Definitions.Def_DedekindSubgroups
public import Definitions.Def_DedekindSubgroups_Solution
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {k : ℕ} [NeZero k]
open Classical

theorem DedekindSubgroups.remark_3_4 (hk : 1 < k) (H : Subgroup (ZMod k)ˣ) :
    ∃ N : ℤ, (N : ℚ) = 12 * k * subgroupSum H ∧
      N ≡ (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2))
        - 4 * ∑ u ∈ (univ.filter (· ∈ H)).filter (fun u => u * u = 1),
            (inv (u : ZMod k).val k : ℤ) [ZMOD 8] := by sorry
