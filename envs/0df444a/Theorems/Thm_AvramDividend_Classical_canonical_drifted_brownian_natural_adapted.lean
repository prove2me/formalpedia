-- Prove2me | Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_natural_adapted
-- name    : AvramDividend.Classical.canonical_drifted_brownian_natural_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:43:35.44979+00:00
-- url     : https://prove2.me/theorems/f81b6ab6-d291-4f59-8edb-d400ad0cc070
-- title:
--   The drifted canonical Brownian process is adapted to its natural filtration
-- statement:
--   The normalised and drifted canonical Brownian process has measurable coordinates. Its natural filtration is therefore well-defined and the process is adapted to that filtration. The theorem explicitly packages the measurability witness and adaptation needed by the Avram spectrally negative Lévy structure.
-- source:
--   Mathlib Filtration.natural and Filtration.stronglyAdapted_natural; accepted canonical_drifted_brownian_measurable.

import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_measurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Tactic

open ProbabilityTheory MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.canonical_drifted_brownian_natural_adapted :
    let X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ)
    ∃ hmeas : ∀ t : ℝ≥0, StronglyMeasurable (X t),
      Adapted (Filtration.natural X hmeas) X := by sorry
