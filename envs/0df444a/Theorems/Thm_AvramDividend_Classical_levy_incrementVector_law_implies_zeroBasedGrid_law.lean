-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_incrementVector_law_implies_zeroBasedGrid_law
-- name    : AvramDividend.Classical.levy_incrementVector_law_implies_zeroBasedGrid_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:15:50.83789+00:00
-- url     : https://prove2.me/theorems/2306113f-95d9-49ba-b55a-102a78f19a3f
-- title:
--   Stationary consecutive increments determine zero-based finite-grid path laws
-- statement:
--   On a deterministic time grid starting at zero, equality of shifted and unshifted consecutive increment-vector laws implies equality of the entire finite vector of shifted path levels. The Lévy path starts at zero, with no scale-function parameters.
-- source:
--   Uses the Proved increment-vector to cumulative-grid-positions law 29b795fb-d20a-4b93-a32d-21561b86c556. This is the exact zero-based grid bridge needed to establish finite-dimensional stationarity and then the strong-Markov barrier splitting child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_incrementVector_law_implies_gridPositions_law

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_incrementVector_law_implies_zeroBasedGrid_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht0 : t 0 = 0) (n : ℕ)
    (hLaw :
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω) P =
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (t (i.val + 1)) ω) P := by
  sorry
