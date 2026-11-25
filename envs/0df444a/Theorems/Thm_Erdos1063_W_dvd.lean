-- Prove2me | Theorems.Thm_Erdos1063_W_dvd
-- name    : Erdos1063.W_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:51.174694+00:00
-- url     : https://prove2.me/theorems/2dc1905f-edcd-5f7c-aa5a-82c9bf12f3c4
-- title:
--   Erdos1063: W dvd
-- statement:
--   **Corollary 5.** `W'_k` divides the exceptional element.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L233-L241
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L233-L241

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.W_dvd {n k i0 : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (hi0 : i0 < k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) : W k ∣ n - i0 := by sorry
