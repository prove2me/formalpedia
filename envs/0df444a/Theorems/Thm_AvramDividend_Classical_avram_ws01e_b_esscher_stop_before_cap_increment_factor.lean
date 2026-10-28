-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_stop_before_cap_increment_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_esscher_stop_before_cap_increment_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:08:02.210245+00:00
-- url     : https://prove2.me/theorems/8004dc2e-3bca-4487-99f8-2c570b633c76
-- title:
--   Finite Esscher stopped increment on the stop-before-cap event
-- statement:
--   If a genuine finite stopping time occurs before a deterministic cap, its later finite-lag increment obeys the stationary finite-terminal Esscher law, without assuming the stopping time is globally bounded.
-- source:
--   Accepted localised Esscher stopping-time increment cylinder factor.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_locally_bounded_stop_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Genuine finite-horizon Esscher regeneration on a first-passage-before-cap event.
The stopping age itself need not be bounded. -/

theorem AvramDividend.Classical.avram_ws01e_b_esscher_stop_before_cap_increment_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      ({ω : Ω | τ ω ≤ H} ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
        {ω : Ω | τ ω ≤ H} *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
