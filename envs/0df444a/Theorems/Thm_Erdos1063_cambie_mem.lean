-- Prove2me | Theorems.Thm_Erdos1063_cambie_mem
-- name    : Erdos1063.cambie_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:58.117635+00:00
-- url     : https://prove2.me/theorems/ca1f5cce-f802-5c72-b4d5-7374f904b0e9
-- title:
--   Erdos1063: cambie mem
-- statement:
--   Cambie's witness is admissible, with exceptional index `0`.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L520-L533
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L520-L533

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.cambie_mem {k : ℕ} (hk : 3 ≤ k) :
    k * (Finset.Icc 1 (k - 1)).lcm id ∈ {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
      ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k} := by sorry
