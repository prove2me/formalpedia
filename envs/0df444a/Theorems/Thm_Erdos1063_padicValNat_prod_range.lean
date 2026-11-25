-- Prove2me | Theorems.Thm_Erdos1063_padicValNat_prod_range
-- name    : Erdos1063.padicValNat_prod_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:35:54.096461+00:00
-- url     : https://prove2.me/theorems/20043daf-6b21-4cfb-9053-738349d7c1ef
-- title:
--   Erdos1063: padic Val Nat prod range
-- statement:
--   The Erdos1063 construction uses the padic Val Nat prod range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L264-L273
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L264-L273

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.padicValNat_prod_range {p : ℕ} [Fact p.Prime] (f : ℕ → ℕ) (m : ℕ)
    (hf : ∀ i < m, f i ≠ 0) :
    padicValNat p (∏ i ∈ Finset.range m, f i) = ∑ i ∈ Finset.range m, padicValNat p (f i) := by sorry
