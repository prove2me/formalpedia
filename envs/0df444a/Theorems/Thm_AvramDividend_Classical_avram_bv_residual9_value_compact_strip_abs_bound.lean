-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_value_compact_strip_abs_bound
-- name    : AvramDividend.Classical.avram_bv_residual9_value_compact_strip_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:16:08.887771+00:00
-- url     : https://prove2.me/theorems/04cdcf26-c925-45ea-8677-5abcab376350
-- title:
--   The continuous original BV value candidate is uniformly bounded on a deterministic finite-horizon reserve strip
-- statement:
--   The candidate w continuous on the nonnegative half-line has a finite nonnegative absolute bound on every compact reserve strip from zero to a finite deterministic ceiling H. This is the continuity-to-integrable-envelope step for controlling the single ruin-contact value in the exact original uniform physical-grid residual.
-- source:
--   AVRAM BV-RESIDUAL9 round-five original BV finite-horizon contact envelope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_value_compact_strip_abs_bound
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ z : ℝ, 0 ≤ z → z ≤ H → |w z| ≤ K := by sorry
