-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_left_ceiling_sampler_basic
-- name    : AvramDividend.Classical.dyadic_left_ceiling_sampler_basic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:08:40.889826+00:00
-- url     : https://prove2.me/theorems/7db06b91-4512-43d6-81b2-ac2ea8a9fb06
-- title:
--   Left dyadic sampler is measurable, past-valued and locally finite-range
-- statement:
--   At dyadic resolution n, round each time upward and subtract one grid step with truncated nonnegative subtraction. The resulting deterministic sampler is Borel measurable, never later than the current time, and takes finitely many values on every bounded interval, including correct treatment at time zero. This supplies the finite-past progressiveness hypotheses for adapted left-continuous dividend controls.
-- source:
--   Dyadic ceiling bounds and finite-index lemmas already Proved in the Avram Dividend development, combined with pinned Mathlib measurability of the natural-number ceiling.

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_bounds
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_mem_finite_grid
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dyadic_left_ceiling_sampler_basic (n : ℕ) :
    let g : ℝ≥0 → ℝ≥0 :=
      fun t : ℝ≥0 => ((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n) - 1 / (2 : ℝ≥0) ^ n
    Measurable g ∧ (∀ t, g t ≤ t) ∧
      (∀ T, (g '' Iic T).Finite) := by sorry
