-- Prove2me | Theorems.Thm_Erdos1063_W_le_n
-- name    : Erdos1063.W_le_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:31:16.810811+00:00
-- url     : https://prove2.me/theorems/a875554b-555c-474b-905c-9bf387a0e68d
-- title:
--   Erdos1063: W le n
-- statement:
--   **Lower bound.** `W'_k ≤ n_k` (whenever an admissible `m` exists, e.g. for `k ≥ 3`
--   by Cambie's bound, formalized by DeepMind's LEAP agent).
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L395-L401
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L395-L401

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.W_le_n {k : ℕ} (hk : 2 ≤ k)
    (hne : {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
      ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}.Nonempty) : W k ≤ n k := by sorry
