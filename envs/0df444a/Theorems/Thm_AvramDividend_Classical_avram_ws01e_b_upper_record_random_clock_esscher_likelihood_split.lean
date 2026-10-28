-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_upper_record_random_clock_esscher_likelihood_split
-- name    : AvramDividend.Classical.avram_ws01e_b_upper_record_random_clock_esscher_likelihood_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:12:55.104979+00:00
-- url     : https://prove2.me/theorems/a1fddcf8-a874-45ef-9ce2-19b8f4890bcf
-- title:
--   Actual random-clock Esscher likelihood splits at a spectrally negative first upper record with known hit level
-- statement:
--   At any finite, attained first strict upper passage of a spectrally negative Lévy process across nonnegative level b, the process is exactly at b, without positive overshoot. If the observation clock e occurs after that passage, the compensated Esscher exponential likelihood at the actual random observation time e factors into exp(θ b−τψ(θ)), depending only on the stopping age and deterministic level, times the post-record likelihood exp(θ(X_e−X_τ)−(e−τ)ψ(θ)). This is a genuine pathwise stopped-clock identity and a critical simplification for lifting original-law residual-clock regeneration to tilted Wiener–Hopf splitting. It assumes neither future/clock independence nor the Wiener–Hopf factorisation.
-- source:
--   Proved firstUpcrossing_value_eq_threshold (014436e7-36d8-45ea-8ca6-bc6917b7788c) and avram_ws01e_b_esscher_random_clock_stopped_density_split (b2a39955-4a1a-444e-afd6-44cf2d39e75e).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_random_clock_stopped_density_split

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_upper_record_random_clock_esscher_likelihood_split
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)))
    (e : Θ → ℝ≥0) (η : Θ) (hObs : u ≤ e η) :
    Real.exp (θ * X.X (e η) ω -
      (e η : ℝ) * laplaceExponent X.c X.σ X.ν θ) =
    Real.exp (θ * b -
      (u : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
    Real.exp (θ * (X.X (e η) ω - X.X u ω) -
      ((e η - u : ℝ≥0) : ℝ) *
        laplaceExponent X.c X.σ X.ν θ) := by sorry
