-- Prove2me | Theorems.Thm_Erdos1063_lcm_facts
-- name    : Erdos1063.lcm_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:50.030081+00:00
-- url     : https://prove2.me/theorems/c91ee422-df6b-5bc5-827c-00e55ba12b75
-- title:
--   Erdos1063: lcm facts
-- statement:
--   The Erdos1063 construction uses the lcm facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L420-L426
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L420-L426

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.lcm_facts {k : ℕ} (hk : 3 ≤ k) :
    (Finset.Icc 1 (k - 1)).lcm id ≠ 0 ∧ 2 ≤ (Finset.Icc 1 (k - 1)).lcm id := by sorry
