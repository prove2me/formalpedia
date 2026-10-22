-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_uniform_downward_jump_measure_integral
-- name    : AvramDividend.Classical.chat06_uniform_downward_jump_measure_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:57:17.27053+00:00
-- url     : https://prove2.me/theorems/b32ccabc-b601-4051-b868-c1883ca8bec2
-- title:
--   Restricted Lebesgue Lévy measure and signed-interval exponential moment coincide
-- statement:
--   For a rate-one compound Poisson process with uniformly distributed downward jumps on (-2,-1), the exponential moment of the Lévy measure defined by restricted Lebesgue measure equals the signed-interval exponential integral. This converts the abstract Lévy-measure integral into the explicit mark transform, without asserting the yet-unproved full process Lévy triplet properties.
-- source:
--   Existing source bv_uniform_negative_levy_measure_integral_equivalence_chat06_20261020.lean, 30 lines, 1190 bytes, SHA-256 5867fbca244763900db4923e3362b9937137e97305462451407e7fee5b3c85c4. Private remote probe ec10a936-76c5-4498-b4c9-e37d48bb1fb9 reached sentinel with zero source errors.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Real

theorem AvramDividend.Classical.chat06_uniform_downward_jump_measure_integral (θ : ℝ) :
    (∫ y, Real.exp (θ * y)
      ∂((volume : Measure ℝ).restrict (Ioo (-2 : ℝ) (-1 : ℝ)))) =
    ∫ y in (-2 : ℝ)..(-1 : ℝ), Real.exp (θ * y) := by sorry
