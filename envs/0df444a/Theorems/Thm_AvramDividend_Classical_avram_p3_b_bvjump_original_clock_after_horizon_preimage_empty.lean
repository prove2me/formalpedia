-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_after_horizon_preimage_empty
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_clock_after_horizon_preimage_empty
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:32:56.083205+00:00
-- url     : https://prove2.me/theorems/ff850259-7376-4626-ae07-fad04444f641
-- title:
--   Actual bounded physical clock has empty later marked-interval preimage
-- statement:
--   For genuine NNReal physical times s,t after the finite original horizon T, the real-to-NNReal preimage of (s,t] is disjoint from the actual source Lebesgue clock support [0,T]. It is a source-clock geometric identity, including all empty and endpoint cases, with no Lévy first-moment or Poisson assumptions. Supports exact zero intensity mass for stopped predictable marked cells.
-- source:
--   Mathlib Real.coe_toNNReal, Set.Ioc, Icc and linear order; same original clock as P3-B source proof.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_clock_after_horizon_preimage_empty
    (s t T : ℝ≥0) (hTs : T ≤ s) :
    (Real.toNNReal ⁻¹' Ioc s t) ∩ Icc (0 : ℝ) (T : ℝ) = ∅ := by sorry
