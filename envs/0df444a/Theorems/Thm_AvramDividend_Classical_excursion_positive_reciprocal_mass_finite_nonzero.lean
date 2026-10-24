-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_positive_reciprocal_mass_finite_nonzero
-- name    : AvramDividend.Classical.excursion_positive_reciprocal_mass_finite_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:56:23.227753+00:00
-- url     : https://prove2.me/theorems/96317a17-cc9d-4e32-bc7c-fdaae5d8ebf3
-- title:
--   Positive reciprocal total mass makes a measure finite and nonzero
-- statement:
--   A measure on the real line with total mass 1/k for k>0 has finite, strictly positive total mass. This validates constructing a nonzero finite measure and its probability normalisation in the excursion resolvent weak-limit argument.
-- source:
--   Preliminary fixed-mass conversion for excursion_laplace_weak_limit_of_tight_approximants; positivity of real inverse and ENNReal.ofReal.

import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory Set

theorem AvramDividend.Classical.excursion_positive_reciprocal_mass_finite_nonzero
    (β : Measure ℝ) (k : ℝ) (hk : 0 < k)
    (hmass : β Set.univ = ENNReal.ofReal (k⁻¹)) :
    β Set.univ < ⊤ ∧ β ≠ 0 := by sorry
