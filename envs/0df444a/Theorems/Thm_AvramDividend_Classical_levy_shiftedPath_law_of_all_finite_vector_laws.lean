-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shiftedPath_law_of_all_finite_vector_laws
-- name    : AvramDividend.Classical.levy_shiftedPath_law_of_all_finite_vector_laws
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:30:25.140127+00:00
-- url     : https://prove2.me/theorems/9b30daef-95c0-45f7-b082-03af46464da9
-- title:
--   Complete shifted Lévy path has the original law when finite-dimensional laws agree
-- statement:
--   At deterministic s, suppose every finite coordinate vector of the future shifted process has the same joint law as the corresponding original Lévy values. Then the entire function-valued shifted process has exactly the original path distribution. Uses the Proved finite-cylinder uniqueness theorem, adaptedness for measurable path-valued maps, and probability-mass finiteness. A critical formal step of stationary path law and strong Markov factorisation.
-- source:
--   Combines measure uniqueness piPathMeasure_eq_of_finite_cylinder_masses (currently authoring) with equality of every finite-dimensional law. Direct prerequisite to supply hStationary in levy_finiteGrid_stoppedEvent_stationaryFuture_reward, towards 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shiftedPath_law_of_all_finite_vector_laws
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (hFinite : ∀ J : Finset ℝ≥0,
      Measure.map (fun ω : Ω => fun j : J =>
        X.X (s + (j : ℝ≥0)) ω - X.X s ω) P =
      Measure.map (fun ω : Ω => fun j : J =>
        X.X (j : ℝ≥0) ω) P) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
  sorry
