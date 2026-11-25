-- Prove2me | Theorems.Thm_DedekindSubgroups_two_mul_k_subgroupSum_modEq
-- name    : DedekindSubgroups.two_mul_k_subgroupSum_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:10:19.883641+00:00
-- url     : https://prove2.me/theorems/25b5a1a9-6452-52c1-80fd-13172a2a862e
-- title:
--   Dedekind Subgroups: two mul k subgroup Sum mod Eq
-- statement:
--   **Corollary 4.1.** If `3 ∤ k` and `H` has odd order `n`, then `2 k S(H,k) ∈ ℤ` and
--   `2 k S(H,k) ≡ 3 n (k-1)(k-2)/2 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L195-L215
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L195-L215

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.two_mul_k_subgroupSum_modEq {k : ℕ} [NeZero k] (hk : 1 < k) (h3 : ¬ 3 ∣ k)
    (H : Subgroup (ZMod k)ˣ) (hodd : Odd (Nat.card H)) :
    ∃ x : ℤ, (x : ℚ) = 2 * k * subgroupSum H ∧
      2 * x ≡ 3 * (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) [ZMOD 16] := by sorry
