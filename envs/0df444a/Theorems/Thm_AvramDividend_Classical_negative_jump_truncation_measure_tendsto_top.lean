-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_tendsto_top
-- name    : AvramDividend.Classical.negative_jump_truncation_measure_tendsto_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:41:38.926013+00:00
-- url     : https://prove2.me/theorems/84c9d677-b598-43ab-9842-dfb87c50e0a1
-- title:
--   Truncated negative jump intensities diverge for an infinite Lévy measure
-- statement:
--   For a measure with infinite mass on the negative half-line, the mass of jumps at most minus one over n plus one tends to infinity as n tends to infinity. The closed negative truncation bands increase to the strictly negative half-line. This supplies the precise diverging Poisson parameters needed in the zero-barrier infinite-activity branch.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and zero-barrier infinite-jump discussion, https://arxiv.org/pdf/math/0702893; continuity from below, Mathlib.MeasureTheory.Measure.MeasureSpace.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.MonotoneConvergence

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- Finite negative-jump truncation intensities exhaust an infinite negative Lévy measure. -/
theorem negative_jump_truncation_measure_tendsto_top
    (ν : Measure ℝ)
    (hν : ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto (fun n : ℕ => ν (Iic (-(1 / ((n : ℝ) + 1)))))
      atTop (nhds (⊤ : ℝ≥0∞)) := by sorry

end AvramDividend.Classical
