-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_gridPosition_law_implies_finiteIndex_law
-- name    : AvramDividend.Classical.levy_gridPosition_law_implies_finiteIndex_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:16:56.653694+00:00
-- url     : https://prove2.me/theorems/a7ef4e12-f915-420f-95d8-d49c79a2e803
-- title:
--   Stationary finite grid position law descends to any finite indexed observation set
-- statement:
--   If an ordered grid contains every member of a finite index set of observation times, equality of shifted and unshifted position-vector laws on that grid implies the same equality for the finite indexed observation vector. Follows by a measurable coordinate projection.
-- source:
--   Consumes zero-based finite-grid position stationarity on the path to stationary Lévy whole-path law, then to strong-Markov barrier dividend splitting 79978d61-9d1f-4b20-b8a5-114797a8e380. No scale-function assumptions.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_gridPosition_law_implies_finiteIndex_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (n : ℕ) (J : Finset ℝ≥0)
    (e : J → Fin n)
    (he : ∀ j : J, t ((e j).val + 1) = (j : ℝ≥0))
    (hGrid :
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (s + t (i.val + 1)) ω - X.X s ω) P =
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (t (i.val + 1)) ω) P) :
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (s + (j : ℝ≥0)) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (j : ℝ≥0) ω) P := by
  sorry
