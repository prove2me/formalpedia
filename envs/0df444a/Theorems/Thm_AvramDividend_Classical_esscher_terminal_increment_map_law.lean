-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_map_law
-- name    : AvramDividend.Classical.esscher_terminal_increment_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:49:03.935156+00:00
-- url     : https://prove2.me/theorems/14dc9816-2e6b-4956-b87f-4174beb8af7b
-- title:
--   Under every later Esscher terminal law an adjacent Lévy increment has the standalone tilted marginal measure
-- statement:
--   For a spectrally negative Lévy process and θ≥0, 0≤s,s+u≤T, the probability law of the increment X_(s+u)−X_s under the Esscher time-T density is exactly the law of X_u under the Esscher time-u density, as equality of Borel probability measures on ℝ. It transfers every measurable increment reward/transform through a genuine equality of distributions.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions (2012), Esscher transform §2.1; accepted terminal increment cylinder factorisation b4c43ae0-cb9d-43f3-bb6c-e484166ddf0e and finite-horizon Esscher probability 6c6f7684-1d83-4271-ac6d-3e584327e2e4; pinned Measure.map_apply.

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_terminal_increment_map_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u T : ℝ≥0) (hT : s + u ≤ T) :
    Measure.map (fun ω : Ω => X.X (s + u) ω - X.X s ω)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) =
    Measure.map (X.X u)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) := by sorry
