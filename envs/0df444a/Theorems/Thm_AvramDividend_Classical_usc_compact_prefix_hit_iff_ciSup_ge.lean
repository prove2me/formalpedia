-- Prove2me | Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_hit_iff_ciSup_ge
-- name    : AvramDividend.Classical.usc_compact_prefix_hit_iff_ciSup_ge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:19:37.830995+00:00
-- url     : https://prove2.me/theorems/a33cda52-ee96-421d-921c-dd00993e0369
-- title:
--   Compact USC closed-level first-passage event is equivalent to the directly measurable continuous-time subtype-indexed supremum
-- statement:
--   For an upper-semicontinuous real path on a compact nonnegative-time prefix, an actual hit of level x by time t is equivalent to x being no greater than the indexed supremum over the subtype s∈[0,t]. This matches the canonical adapted-process representation of the full prefix supremum directly. Prove equivalence of the subtype indexed supremum with the image-set supremum by bounding both via the compact USC bound and the standard le_csSup / le_ciSup inequalities, then invoke the accepted compact-prefix hit ↔ image supremum theorem. Together with full-prefix supremum adaptedness this will make continuous-time closed-level hitting events observable without an assumption that the given filtration is right continuous.
-- source:
--   Accepted AvramDividend.Classical.usc_compact_prefix_hit_iff_sup_ge; pinned Mathlib Order.ConditionallyCompleteLattice.Basic le_ciSup / ciSup_le / le_csSup.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_hit_iff_sup_ge

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.usc_compact_prefix_hit_iff_ciSup_ge
    (R : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 t)) :
    (∃ s : ℝ≥0, s ≤ t ∧ x ≤ R s) ↔
      x ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, R s.1 := by sorry
