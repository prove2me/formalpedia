-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_random_measure_time_horizon_lintegral_iSup
-- name    : AvramDividend.Classical.nonnegative_random_measure_time_horizon_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T12:03:53.013255+00:00
-- url     : https://prove2.me/theorems/54d9829a-29b7-42ad-8f1e-2a2ad7c8ca97
-- title:
--   Random dividend measure expected integral recovered from finite time horizons
-- statement:
--   Given a measurable random nonnegative integrand and measurable finite-horizon random-measure integrals, the full expected integral over nonnegative times equals the supremum of finite-horizon expected integrals. This supplies the outer monotone-convergence step after stochastic finite-horizon dividend verification.
-- source:
--   Mathlib.MeasureTheory.Integral.Lebesgue.Add: lintegral_iSup, and the canonically Proved nonnegative_time_horizon_lintegral_iSup.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_nonnegative_time_horizon_lintegral_iSup

open MeasureTheory Set
open scoped Classical ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nonnegative_random_measure_time_horizon_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (μ : Ω → Measure ℝ)
    (f : Ω → ℝ → ℝ≥0∞)
    (hf : ∀ ω, Measurable (f ω))
    (hMeas : ∀ n : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in Icc (0 : ℝ) (n : ℝ), f ω t ∂(μ ω))) :
    (∫⁻ ω, (∫⁻ t in Ici (0 : ℝ), f ω t ∂(μ ω)) ∂P) =
      ⨆ n : ℕ, (∫⁻ ω, (∫⁻ t in Icc (0 : ℝ) (n : ℝ),
        f ω t ∂(μ ω)) ∂P) := by sorry
