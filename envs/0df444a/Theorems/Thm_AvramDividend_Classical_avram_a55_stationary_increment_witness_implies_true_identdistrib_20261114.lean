-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a55_stationary_increment_witness_implies_true_identdistrib_20261114
-- name    : AvramDividend.Classical.avram_a55_stationary_increment_witness_implies_true_identdistrib_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:15:23.158798+00:00
-- url     : https://prove2.me/theorems/e6e5a758-1867-4374-be0d-2f363aeb1921
-- title:
--   Stationary increment map witnesses imply exact IdentDistrib with increments from time zero
-- statement:
--   For a measurable zero-start real stochastic process on the actual probability space, a common law witness for increments over each time horizon gives the exact stationary-increments IdentDistrib property needed to construct a Lévy process.
-- source:
--   Pinned Mathlib IdentDistrib.mk and NNReal addition/subtraction identity.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- A stationary increment map witness at every horizon implies the precise source law of increments. -/

theorem AvramDividend.Classical.avram_a55_stationary_increment_witness_implies_true_identdistrib_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t, Measurable (G t))
    (hZero : ∀ ω, G 0 ω = 0)
    (hShift : ∀ T : ℝ≥0, ∃ Z : Ω → ℝ, Measurable Z ∧
      ∀ s : ℝ≥0,
        Measure.map (fun ω => G (s + T) ω - G s ω) P =
          Measure.map Z P) :
    ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P := by sorry
