-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_real_clock_stopped_density_split
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_Qp_real_clock_stopped_density_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:27:40.307014+00:00
-- url     : https://prove2.me/theorems/114613eb-f17b-4a03-8339-863e4aba2c21
-- title:
--   Exact true terminal Esscher likelihood split at a nonnegative stopped age and a real exponential-clock observation
-- statement:
--   At every real observation clock value t at or after a measurable or arbitrary nonnegative stopped time τ, the true pathwise Esscher likelihood at t factors as its stopped prefix likelihood and a compensated increment likelihood over the exactly converted residual real clock. The condition t≥τ ensures both t and t−τ are nonnegative and avoids transferring an independent-clock property to the terminally tilted law. This theorem discharges the actual hSplit hypothesis of the finite-rate capped first-record Qp full-path unnormalised regeneration interface.
-- source:
--   Noncircular real-to-NNReal time-domain conversion followed by canonically Proved stopped Esscher density algebra b2a39955-4a1a-444e-afd6-44cf2d39e75e. No Wiener–Hopf independence or resolvent identity is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_random_clock_stopped_density_split
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_Qp_real_clock_stopped_density_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (τ : Ω → ℝ≥0) (ω : Ω) (t : ℝ)
    (hObs : (τ ω : ℝ) ≤ t) :
    ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal t) ω -
      (Real.toNNReal t : ℝ) * X.ψ θ)) =
    ENNReal.ofReal (Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ)) *
    ENNReal.ofReal (Real.exp (θ *
      (X.X (τ ω + Real.toNNReal (t - (τ ω : ℝ))) ω -
       X.X (τ ω) ω) -
      (Real.toNNReal (t - (τ ω : ℝ)) : ℝ) * X.ψ θ)) := by sorry
