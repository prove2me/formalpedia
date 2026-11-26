-- Prove2me | Theorems.Thm_Auto_aux_discreteAverage_congr_on
-- name    : Auto.aux_discreteAverage_congr_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:43:09.440232+00:00
-- url     : https://prove2.me/theorems/ba16118c-19a2-41a2-a0d7-58cbe9ae2752
-- title:
--   Auto: aux discrete Average congr on
-- statement:
--   The Auto construction uses the aux discrete Average congr on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2168-L2179
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2168-L2179

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_discreteAverage_congr_on {n : ℕ} (N : ℕ)
    (F G : Fin n → (Fin n → ℕ) → ℝ) (k : Fin n → ℕ)
    (h : ∀ i m, m ∈ Finset.range N →
      F i (k + aux_coordinate i m) = G i (k + aux_coordinate i m)) :
    aux_discreteAverage N F k = aux_discreteAverage N G k := by sorry
