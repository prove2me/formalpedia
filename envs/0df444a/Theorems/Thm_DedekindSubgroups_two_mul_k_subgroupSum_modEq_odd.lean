-- Prove2me | Theorems.Thm_DedekindSubgroups_two_mul_k_subgroupSum_modEq_odd
-- name    : DedekindSubgroups.two_mul_k_subgroupSum_modEq_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:13:25.183019+00:00
-- url     : https://prove2.me/theorems/d4d36de3-9acd-5ee0-b6cf-257d98aa23dd
-- title:
--   Dedekind Subgroups: two mul k subgroup Sum mod Eq odd
-- statement:
--   Corollary 4.1 for odd `k`: `2 k S(H,k) ≡ n k (k-1)/2 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L218-L229
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L218-L229

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.two_mul_k_subgroupSum_modEq_odd {k : ℕ} [NeZero k] (hk : 1 < k) (h3 : ¬ 3 ∣ k)
    (hkodd : Odd k) (H : Subgroup (ZMod k)ˣ) (hodd : Odd (Nat.card H)) :
    ∃ x : ℤ, (x : ℚ) = 2 * k * subgroupSum H ∧
      2 * x ≡ (Nat.card H : ℤ) * ((k : ℤ) * ((k : ℤ) - 1)) [ZMOD 16] := by sorry
