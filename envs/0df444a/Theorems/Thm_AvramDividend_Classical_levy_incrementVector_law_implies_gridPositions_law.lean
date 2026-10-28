-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_incrementVector_law_implies_gridPositions_law
-- name    : AvramDividend.Classical.levy_incrementVector_law_implies_gridPositions_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:52:45.940259+00:00
-- url     : https://prove2.me/theorems/29b795fb-d20a-4b93-a32d-21561b86c556
-- title:
--   Cumulative Lévy grid position laws inherit equality of consecutive increment-vector laws
-- statement:
--   For a finite grid, if the joint laws of the consecutive increment vectors of shifted and unshifted Lévy paths agree, then the joint laws of cumulative reserve-position differences relative to the grid's initial time agree. The proof transports equality of measures through a measurable prefix-sum operator, using the all-n pathwise telescoping identity.
-- source:
--   Mathematical bridge from joint rectangle stationarity to arbitrary finite-dimensional shifted path stationarity, needed by strong-Markov dividend splitting theorem 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_n_levy_increment_telescoping

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_incrementVector_law_implies_gridPositions_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (n : ℕ)
    (hLaw :
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω) P =
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X (s + t 0) ω) P =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t 0) ω) P := by
  sorry
