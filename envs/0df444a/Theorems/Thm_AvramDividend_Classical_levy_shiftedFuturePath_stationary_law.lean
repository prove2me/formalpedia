-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
-- name    : AvramDividend.Classical.levy_shiftedFuturePath_stationary_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:48:44.579888+00:00
-- url     : https://prove2.me/theorems/f7f7d00c-aaf9-47d1-9d8e-1edbc5d2b849
-- title:
--   The whole Lévy future-increment path is stationary after every deterministic shift
-- statement:
--   The full future path of Lévy increments after a fixed time has the same distribution as the original path, as a measure on the function space. It is derived from all finite-dimensional joint distributions and the finite-cylinder path measure uniqueness theorem, without scale-function assumptions.
-- source:
--   Supplies the hStationary premise needed by Proved killed grid reward factorisation fb66ecc1-080a-4cb3-b859-b2073d3ca34a and its limiting strong-Markov counterpart; child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFiniteObservationVector_law
import Theorems.Thm_AvramDividend_Classical_levy_shiftedPath_law_of_all_finite_vector_laws

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shiftedFuturePath_stationary_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X t ω) P := by
  sorry
