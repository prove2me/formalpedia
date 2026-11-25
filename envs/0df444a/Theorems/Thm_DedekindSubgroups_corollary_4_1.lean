-- Prove2me | Theorems.Thm_DedekindSubgroups_corollary_4_1
-- name    : DedekindSubgroups.corollary_4_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:14:48.780665+00:00
-- url     : https://prove2.me/theorems/f9cdf162-0343-585e-9474-b2518d9d88b6
-- title:
--   Dedekind Subgroups: corollary 4 1
-- statement:
--   **Corollary 4.1.** If `3 ∤ k` and `H` has odd order `n`, then `2 k S(H,k) ∈ ℤ` and
--   `2 k S(H,k) ≡ 3 n (k-1)(k-2)/2 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/Solution.lean#L55-L59
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/Solution.lean#L55-L59

module
public import Definitions.Def_DedekindSubgroups
public import Definitions.Def_DedekindSubgroups_Solution
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.corollary_4_1 {k : ℕ} [NeZero k] (hk : 1 < k) (h3 : ¬ 3 ∣ k)
    (H : Subgroup (ZMod k)ˣ) (hodd : Odd (Nat.card H)) :
    ∃ x : ℤ, (x : ℚ) = 2 * k * subgroupSum H ∧
      2 * x ≡ 3 * (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) [ZMOD 16] := by sorry
