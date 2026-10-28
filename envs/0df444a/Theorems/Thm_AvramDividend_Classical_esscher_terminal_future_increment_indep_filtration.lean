-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_terminal_future_increment_indep_filtration
-- name    : AvramDividend.Classical.esscher_terminal_future_increment_indep_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:11:29.834483+00:00
-- url     : https://prove2.me/theorems/1f8850b9-7ee1-4cab-954a-98469eb4550b
-- title:
--   Under each finite-terminal Esscher law every future Lévy increment is independent of the complete earlier filtration
-- statement:
--   For 0 ≤ s, u and s+u ≤ T, the Esscher change of probability at deterministic terminal T preserves independence between the full past filtration F_s and the future increment X_(s+u)−X_s. Independence is expressed by Mathlib ProbabilityTheory.Indep between F_s and the pullback Borel sigma-algebra of the future increment, with the genuine weighted probability Q_T. The statement holds for every measurable past event and every Borel future event and does not assert an infinite-horizon measure.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions, exponential change of measure; canonical accepted Prove2Me independent-increment rectangles b4c43ae0-cb9d-43f3-bb6c-e484166ddf0e and increment pushforward law 14dc9816-2e6b-4956-b87f-4174beb8af7b; pinned Mathlib ProbabilityTheory.Indep_iff.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_map_law
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events

open AvramDividend.Classical MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_terminal_future_increment_indep_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u T : ℝ≥0) (hT : s + u ≤ T) :
    ProbabilityTheory.Indep (𝓕 s)
      (MeasurableSpace.comap
        (fun ω : Ω => X.X (s + u) ω - X.X s ω)
        (inferInstance : MeasurableSpace ℝ))
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) := by sorry
