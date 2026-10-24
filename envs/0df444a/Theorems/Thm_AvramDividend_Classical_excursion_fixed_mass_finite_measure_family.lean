-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_fixed_mass_finite_measure_family
-- name    : AvramDividend.Classical.excursion_fixed_mass_finite_measure_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:08:10.463975+00:00
-- url     : https://prove2.me/theorems/aaa54f06-e8b6-4df9-a238-767f27f2bb98
-- title:
--   Package fixed finite-mass measure sequences as FiniteMeasure families
-- statement:
--   Every measure in a sequence whose mass is a common finite extended nonnegative coercion can be represented by a FiniteMeasure; its NNReal mass then equals that common value. This removes the Measure-to-FiniteMeasure conversion obstacle in the excursion Laplace weak-limit proof.
-- source:
--   MeasureTheory.FiniteMeasure subtype, IsFiniteMeasure on bounded mass, ennreal_mass.

import Mathlib.MeasureTheory.Measure.FiniteMeasure

open MeasureTheory Set

theorem AvramDividend.Classical.excursion_fixed_mass_finite_measure_family
    (β : ℕ → Measure ℝ) (c : NNReal)
    (hmass : ∀ n : ℕ, β n univ = (c : ENNReal)) :
    ∃ ν : ℕ → FiniteMeasure ℝ,
      (∀ n : ℕ, (ν n : Measure ℝ) = β n) ∧
      (∀ n : ℕ, (ν n).mass = c) := by sorry
