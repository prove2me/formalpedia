-- Prove2me | Theorems.Thm_Erdos1063_prod_range_succ_eq_factorial
-- name    : Erdos1063.prod_range_succ_eq_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:35:28.470192+00:00
-- url     : https://prove2.me/theorems/10ca5c8d-63f3-57bb-bb70-127113e2a86e
-- title:
--   Erdos1063: prod range succ eq factorial
-- statement:
--   The Erdos1063 construction uses the prod range succ eq factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L275-L278
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L275-L278

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.prod_range_succ_eq_factorial (m : ℕ) : ∏ y ∈ Finset.range m, (y + 1) = m ! := by sorry
