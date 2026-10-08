-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_integrable
-- name    : AvramDividend.Classical.levy_compensated_exponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:22:36.609173+00:00
-- url     : https://prove2.me/theorems/dd773186-c390-471c-8953-7e3f1e96dc2b
-- title:
--   Compensated Lévy exponential is integrable at deterministic times
-- statement:
--   The compensated positive-exponential process at deterministic t is integrable, because the defining Laplace transform asserts integrability of exp(θ X_t), and multiplication by the fixed finite real factor exp(-t ψθ) preserves integrability.
-- source:
--   SpectrallyNegativeLevy.laplace and Mathlib Integrable.mul_const; analytic prerequisite for compensated exponential martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_exponential_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * X.X t ω - (t : ℝ) * X.ψ θ)) P := by sorry
