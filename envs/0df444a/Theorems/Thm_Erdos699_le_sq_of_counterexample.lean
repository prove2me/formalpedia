-- Prove2me | Theorems.Thm_Erdos699_le_sq_of_counterexample
-- name    : Erdos699.le_sq_of_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:31.7702+00:00
-- url     : https://prove2.me/theorems/a7541f31-aee2-594b-865b-8238f46e57c7
-- title:
--   Erdos699: le sq of counterexample
-- statement:
--   If no prime `p ≥ i` divides `gcd(C(n, i), C(n, j))`, with `1 ≤ i < j ≤ n / 2`, then
--   `n ≤ j²`.
--
--   Source: https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L124-L160
-- source:
--   https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L124-L160

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
set_option autoImplicit false
@[expose] public section
public section
open Erdos699

theorem Erdos699.le_sq_of_counterexample {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n / 2)
    (hcon : ∀ p : ℕ, p.Prime → i ≤ p → ¬ p ∣ Nat.gcd (n.choose i) (n.choose j)) :
    n ≤ j ^ 2 := by sorry
