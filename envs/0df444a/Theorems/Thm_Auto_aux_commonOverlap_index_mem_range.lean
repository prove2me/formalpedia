-- Prove2me | Theorems.Thm_Auto_aux_commonOverlap_index_mem_range
-- name    : Auto.aux_commonOverlap_index_mem_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:23.387936+00:00
-- url     : https://prove2.me/theorems/d7a33b80-bfd9-403a-95e9-8e2b2926f9bb
-- title:
--   Auto: aux common Overlap index mem range
-- statement:
--   A common overlap contributing to the interval `[0,N)` has an index in
--   `range N`.  The open upper faces of the cuboids remove endpoint terms.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L941-L969
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L941-L969

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

theorem Auto.aux_commonOverlap_index_mem_range {n : ℕ} (hn : 0 < n)
    {ε δ : ℝ} (hwidth : ε + δ < 1) (u : aux_RVector n)
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) (N : ℕ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) N) (m : ℤ)
    (hm : ∀ i, ε - u i ≤ s - (m : ℝ) ∧
      s - (m : ℝ) < ε + δ - u i) :
    ∃ q : Fin N, (q.val : ℤ) = m := by sorry
