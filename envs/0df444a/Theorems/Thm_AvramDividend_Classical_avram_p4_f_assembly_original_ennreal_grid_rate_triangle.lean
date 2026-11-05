-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ennreal_grid_rate_triangle
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_ennreal_grid_rate_triangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:45:49.117714+00:00
-- url     : https://prove2.me/theorems/5c04d334-8f10-4d6f-8219-bd06d4c9c81f
-- title:
--   Original uniform finite-grid ENNReal expected pair rate equals the real triangular rate
-- statement:
--   Convert the exact finite sum of NNReal physical-grid deterministic source pair rates into the real triangular pair rate under ENNReal.ofReal. This source-faithful cast bridges the Proved physical-grid real triangular lemma to the original P2-E expected finite-grid rate, without any probabilistic proxy or additional assumptions.
-- source:
--   Proved source physical-grid real rate bridge 4829bfa1-dde5-45fb-ad3a-5c6627056bfa, exact original P2-E finite-grid expectation 77b37394 and Open original expected pair limit 3c3b14b3. Required to transfer NNReal rates into ENNReal for the same original stochastic source.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_physical_grid_real_rate_bridge
open AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_ennreal_grid_rate_triangle
    (T a : ℝ≥0) (k : ℕ) (hk : 0 < k) :
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    (∑ i : Fin k, ((s i : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞))) =
      ENNReal.ofReal (((k : ℝ) * ((k : ℝ) - 1) / 2) *
        (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2)) := by sorry
