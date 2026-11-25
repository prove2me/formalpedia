-- Prove2me | Theorems.Thm_Erdos1063_valuation_bound
-- name    : Erdos1063.valuation_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:46.786639+00:00
-- url     : https://prove2.me/theorems/27bfc683-494f-587f-9aa4-5a9667ce60bc
-- title:
--   Erdos1063: valuation bound
-- statement:
--   **Corollary 5, one prime.** Only the divisibility of the *other* elements is used;
--   not even `i0 < k` is needed.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L206-L210
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L206-L210

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.valuation_bound {n k p i0 : ℕ} (hp : p.Prime) (hkn : 2 * k ≤ n) (hpk : p ∣ k)
    (hk : 2 ≤ k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) :
    padicValNat p k + Nat.log p (k - 1) ≤ padicValNat p (n - i0) := by sorry
