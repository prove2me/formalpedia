-- Prove2me | Theorems.Thm_Auto_aux_mem_commonOverlapSet_iff
-- name    : Auto.aux_mem_commonOverlapSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:01.927129+00:00
-- url     : https://prove2.me/theorems/ba78d895-75fa-5890-8cff-791001e44efb
-- title:
--   Auto: aux mem common Overlap Set iff
-- statement:
--   The common-overlap condition is a half-open interval condition.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L687-L712
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L687-L712

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

theorem Auto.aux_mem_commonOverlapSet_iff {n : ℕ} (hn : 0 < n)
    {ε δ s : ℝ} (u : aux_RVector n) (m : ℕ) :
    s ∈ aux_commonOverlapSet ε δ u m ↔
      s ∈ Ico (aux_overlapLower hn ε u m) (aux_overlapUpper hn ε δ u m) := by sorry
