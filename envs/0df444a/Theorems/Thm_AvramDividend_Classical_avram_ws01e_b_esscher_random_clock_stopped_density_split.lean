-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_random_clock_stopped_density_split
-- name    : AvramDividend.Classical.avram_ws01e_b_esscher_random_clock_stopped_density_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:09:43.17188+00:00
-- url     : https://prove2.me/theorems/b2a39955-4a1a-444e-afd6-44cf2d39e75e
-- title:
--   Exact stopped-time Esscher likelihood factorisation at an independent observation clock
-- statement:
--   For a genuine Lévy path, any random stopping time τ(ω) at or before an observation clock e(η), and any real Esscher parameter θ, the compensated exponential likelihood at time e factors pointwise into the likelihood up to τ and the likelihood of the remaining path increment over e−τ. This uses a true realised observation time rather than a deterministic clock substitute; it is algebraic and assumes no stochastic independence or Wiener–Hopf splitting.
-- source:
--   Direct random-time specialisation of Proved esscher_compensated_exp_time_split (481efeaf-b470-4451-aa29-0daf9fa3117b) and NNReal add_tsub_cancel_of_le.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_compensated_exp_time_split

open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.avram_ws01e_b_esscher_random_clock_stopped_density_split
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (τ : Ω → ℝ≥0)
    (e : Θ → ℝ≥0) (ω : Ω) (η : Θ)
    (hObs : τ ω ≤ e η) :
    Real.exp
      (θ * X.X (e η) ω -
        (e η : ℝ) * laplaceExponent X.c X.σ X.ν θ) =
    Real.exp
      (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
    Real.exp
      (θ * (X.X (e η) ω - X.X (τ ω) ω) -
        ((e η - τ ω : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ) := by sorry
