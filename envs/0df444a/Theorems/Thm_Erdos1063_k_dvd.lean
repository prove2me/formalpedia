-- Prove2me | Theorems.Thm_Erdos1063_k_dvd
-- name    : Erdos1063.k_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:35:25.728935+00:00
-- url     : https://prove2.me/theorems/b1d713b0-a007-4ecf-9f66-79aed1c1b7e8
-- title:
--   Erdos1063: k dvd
-- statement:
--   **The failing index is `n mod k`.** Under the same hypothesis as `W_dvd`, `k ∣ n - i0`;
--   in particular `i0 = n % k` when `i0 < k`.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L254-L256
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L254-L256

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.k_dvd {n k i0 : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (hi0 : i0 < k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) : k ∣ n - i0 := by sorry
