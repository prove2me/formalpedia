-- Prove2me | Theorems.Thm_Erdos1063_valuation_bound_aux
-- name    : Erdos1063.valuation_bound_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:31:12.206841+00:00
-- url     : https://prove2.me/theorems/687ce5a8-c03d-496e-9144-55150e21120d
-- title:
--   Erdos1063: valuation bound aux
-- statement:
--   Core statement: `v_p(C(n,k)) + v_p(k) ≤ v_p(n - i0)` and
--   `v_p(k) + ⌊log_p (k-1)⌋ ≤ v_p(n - i0)`.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L78-L202
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L78-L202

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.valuation_bound_aux {n k p i0 : ℕ} (hp : p.Prime) (hkn : 2 * k ≤ n) (hpk : p ∣ k)
    (hk : 2 ≤ k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) :
    padicValNat p (n.choose k) + padicValNat p k ≤ padicValNat p (n - i0) ∧
      padicValNat p k + Nat.log p (k - 1) ≤ padicValNat p (n - i0) := by sorry
