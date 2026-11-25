-- Prove2me | Theorems.Thm_DedekindSubgroups_twelve_mul_subgroupSum_modEq_eight
-- name    : DedekindSubgroups.twelve_mul_subgroupSum_modEq_eight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:07:58.86594+00:00
-- url     : https://prove2.me/theorems/305fab13-8d14-4606-b5f4-e1ee43e175ec
-- title:
--   Dedekind Subgroups: twelve mul subgroup Sum mod Eq eight
-- statement:
--   **Remark 3.4.** For every subgroup `H` of `(ℤ/kℤ)ˣ`, `12 k S(H,k)` is an integer congruent to
--   `|H|(k-1)(k-2) - 4 ∑_{h ∈ H, h² = 1} I(h,k)` modulo `8`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/General.lean#L20-L74
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/General.lean#L20-L74

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_General
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {k : ℕ} [NeZero k]
open Classical

theorem DedekindSubgroups.twelve_mul_subgroupSum_modEq_eight (hk : 1 < k) (H : Subgroup (ZMod k)ˣ) :
    ∃ N : ℤ, (N : ℚ) = 12 * k * subgroupSum H ∧
      N ≡ (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2))
        - 4 * ∑ u ∈ (univ.filter (· ∈ H)).filter (fun u => u * u = 1),
            (inv (u : ZMod k).val k : ℤ) [ZMOD 8] := by sorry
