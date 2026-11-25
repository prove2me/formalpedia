-- Prove2me | Theorems.Thm_DedekindSubgroups_two_mul_subgroupSum_prime
-- name    : DedekindSubgroups.two_mul_subgroupSum_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:10:27.838679+00:00
-- url     : https://prove2.me/theorems/04be6c5a-3b97-53ac-bafd-2355a898ffc6
-- title:
--   Dedekind Subgroups: two mul subgroup Sum prime
-- statement:
--   **Theorem 1.2.** Let `p > 3` be prime and `H ≤ (ℤ/pℤ)ˣ` of odd order `n > 1`. Then `2 S(H,p)`
--   is an integer and `2 S(H,p) ≡ n (p-1)/2 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L233-L307
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L233-L307

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.two_mul_subgroupSum_prime {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ y : ℤ, (y : ℚ) = 2 * subgroupSum H ∧
      y ≡ (Nat.card H : ℤ) * (((p : ℤ) - 1) / 2) [ZMOD 8] := by sorry
