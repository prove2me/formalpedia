-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_endpoint_markov_bound
-- name    : AvramDividend.Classical.chat04_esscher_finite_negative_endpoint_markov_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:53:16.612854+00:00
-- url     : https://prove2.me/theorems/18f54948-a533-417b-9219-381bf7aef7f7
-- title:
--   Markov bound for a negative Lévy endpoint under the actual finite-time Esscher law
-- statement:
--   For θ≥ε≥0, time t and level b, the finite Esscher probability of the event exp(−εX_t)≥exp(εb), multiplied by exp(εb), is at most exp(t[ψ(θ−ε)−ψ(θ)]). This is the exact exponential Chernoff bound, in ENNReal form, for a downward endpoint excursion under the truly constructed finite Esscher law.
-- source:
--   Use the pinned nonnegative integral Markov inequality `mul_meas_ge_le_lintegral` with measurable exp(−εX_t), then substitute the proven finite negative Esscher ENNReal Laplace identity. This is a nonasymptotic step toward the grid downward-ruin tail, independent of Wiener–Hopf.

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_laplace_lintegral_exact
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_finite_negative_endpoint_markov_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε b : ℝ)
    (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ) :
    ENNReal.ofReal (Real.exp (ε * b)) *
      (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal
        (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))
        {ω : Ω | ENNReal.ofReal (Real.exp (ε * b)) ≤
          ENNReal.ofReal (Real.exp (-ε * X.X t ω))} ≤
      ENNReal.ofReal
        (Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) := by sorry
