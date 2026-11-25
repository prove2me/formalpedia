-- Prove2me | Theorems.Thm_Erdos1063_index_eq_mod
-- name    : Erdos1063.index_eq_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:35:10.049088+00:00
-- url     : https://prove2.me/theorems/c36463d7-5a9e-5e03-b0be-1a3b55381d71
-- title:
--   Erdos1063: index eq mod
-- statement:
--   The Erdos1063 construction uses the index eq mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L258-L262
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L258-L262

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.index_eq_mod {n k i0 : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (hi0 : i0 < k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) : i0 = n % k := by sorry
