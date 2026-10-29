-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_observation_or_horizon_stopping_ws01c
-- name    : AvramDividend.Classical.bv_observation_or_horizon_stopping_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:54:25.328347+00:00
-- url     : https://prove2.me/theorems/30032f11-a174-4e96-a28d-121bce9cdbdd
-- title:
--   A strict grid observation with finite fallback is a stopping time
-- statement:
--   An adapted real observation at time t, compared strictly with a lower barrier, gives a genuine two-valued original-filtration stopping clock: t on a strict hit, or deterministic later H otherwise. The proof needs no right-continuous augmentation.
-- source:
--   Causal repair of terminal failed job eb14b773-4475-4e4c-b1e9-9e54e9454df2. Its old preamble opened an unavailable project namespace and had unresolved Filtration/IsStoppingTime; Mathlib plus MeasureTheory supplies these, preserving the exact theorem proposition and original filtration. Proof source work/avram_ws01c_observation_horizon_stop_solution_repair_20261028.lean.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_observation_or_horizon_stopping_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ)
    (g : Ω → ℝ) (t H : ℝ≥0) (htH : t ≤ H)
    (hg : Measurable[ℱ t] g) (b : ℝ) :
    IsStoppingTime ℱ
      (fun ω : Ω => ((if g ω < b then t else H : ℝ≥0) :
        WithTop ℝ≥0)) := by sorry
