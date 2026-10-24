-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_fixed_mass_normalization_preserves_tightness
-- name    : AvramDividend.Classical.excursion_fixed_mass_normalization_preserves_tightness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:58:19.981778+00:00
-- url     : https://prove2.me/theorems/1d2aefcb-bf38-452e-b79b-8c4c9348df5d
-- title:
--   Fixed positive-mass normalisation preserves tightness
-- statement:
--   For finite real measures with the same positive mass and a uniformly tight family, their probability normalisations remain uniformly tight. This enables the Prokhorov subsequence theorem in the fixed-mass excursion Laplace weak-limit argument.
-- source:
--   Tightness compact-complement criterion, FiniteMeasure.toMeasure_normalize_eq_of_nonzero and ENNReal inverse cancellation. Fixed common mass avoids uncontrolled normalising constants.

import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.excursion_fixed_mass_normalization_preserves_tightness
    (ν : ℕ → FiniteMeasure ℝ) (c : NNReal) (hc : 0 < c)
    (hmass : ∀ n : ℕ, (ν n).mass = c)
    (hnz : ∀ n : ℕ, ν n ≠ 0)
    (htight : IsTightMeasureSet
      (Set.range (fun n : ℕ => (ν n : Measure ℝ)))) :
    IsTightMeasureSet
      (Set.range (fun n : ℕ => ((ν n).normalize : Measure ℝ))) := by sorry
