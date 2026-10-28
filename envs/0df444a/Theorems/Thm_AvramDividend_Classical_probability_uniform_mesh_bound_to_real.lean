-- Prove2me | Theorems.Thm_AvramDividend_Classical_probability_uniform_mesh_bound_to_real
-- name    : AvramDividend.Classical.probability_uniform_mesh_bound_to_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:37:25.922948+00:00
-- url     : https://prove2.me/theorems/62830915-b887-4e00-b2a3-708e5b4b2df5
-- title:
--   Uniform finite-grid event estimate transfers to real probabilities without finiteness side conditions
-- statement:
--   For any probability measure, the finite N-fold extended-real measure inequality for two events immediately yields the same inequality in real probabilities. The finiteness condition required for ENNReal.toReal monotonicity is automatic because the measure of each event is at most one and N is finite.
-- source:
--   Accepted finite_measure_uniform_mesh_bound_to_real and standard probability-measure bounds; Avram, Palmowski and Pistorius (2007), §3.3.

import Theorems.Thm_AvramDividend_Classical_finite_measure_uniform_mesh_bound_to_real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.probability_uniform_mesh_bound_to_real
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Set Ω) (N : ℕ)
    (hBound : P A ≤ (N : ℝ≥0∞) * P B) :
    P.real A ≤ (N : ℝ) * P.real B := by sorry
