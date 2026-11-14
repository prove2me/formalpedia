-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass
-- name    : AvramDividend.Classical.avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:54:19.755639+00:00
-- url     : https://prove2.me/theorems/ea25ca37-85c3-4a83-9079-9fb19eefda9e
-- title:
--   Original physical [0,T] Lebesgue time pushed to NNReal has finite total mass
-- statement:
--   The original physical bounded time measure used in all BVB fullmask Lévy compensators is the pushforward under Real.toNNReal of Lebesgue restricted to Icc 0 T. For T>0 it has finite full mass, since the source Lebesgue restricted interval is finite and the measurable map does not increase total mass. This enables the source exact nested compensator uniform bound BVB68 by a finite-time Bochner integral bound.
-- source:
--   Mathlib finite real interval measure, Measure.map_apply measurable Real.toNNReal, exact original BVB68 time source.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass
    (T : ℝ) (hT : 0 < T) :
    ((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
      Set.univ) < ⊤ := by sorry
