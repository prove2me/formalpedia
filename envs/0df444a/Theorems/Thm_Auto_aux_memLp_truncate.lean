-- Prove2me | Theorems.Thm_Auto_aux_memLp_truncate
-- name    : Auto.aux_memLp_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:50:57.345727+00:00
-- url     : https://prove2.me/theorems/ba12f21b-e927-4fd4-977f-94a1a7ca2316
-- title:
--   Auto: aux mem Lp truncate
-- statement:
--   The Auto construction uses the aux mem Lp truncate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2204-L2208
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2204-L2208

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

theorem Auto.aux_memLp_truncate {n : ℕ} (A : Finset (Fin n → ℕ))
    (F : (Fin n → ℕ) → ℝ) (p : ℝ≥0∞) (hF : MemLp F p Measure.count) :
    MemLp (aux_truncate A F) p Measure.count := by sorry
