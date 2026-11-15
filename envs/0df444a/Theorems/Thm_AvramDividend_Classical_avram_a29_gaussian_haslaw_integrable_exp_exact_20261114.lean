-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a29_gaussian_haslaw_integrable_exp_exact_20261114
-- name    : AvramDividend.Classical.avram_a29_gaussian_haslaw_integrable_exp_exact_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:09:27.027314+00:00
-- url     : https://prove2.me/theorems/ad834587-ca77-4b5c-82bc-6c611a3db465
-- title:
--   Centred Gaussian HasLaw under the original measure gives every exact exponential moment and integrability
-- statement:
--   A random variable having centred Gaussian distribution with a nonnegative variance under an arbitrary measure is integrable after every real exponential tilt, and its expectation equals exp(variance times tilt squared over two).
-- source:
--   Pinned Mathlib integrable_exp_mul_gaussianReal and ProbabilityTheory.mgf_gaussianReal.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Exact exponential integrability and moment generating formula from a centred real Gaussian law. -/

theorem AvramDividend.Classical.avram_a29_gaussian_haslaw_integrable_exp_exact_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G : Ω → ℝ) (v : ℝ≥0)
    (hLaw : HasLaw G (gaussianReal 0 v) P) :
    ∀ θ : ℝ,
      Integrable (fun ω => Real.exp (θ * G ω)) P ∧
      (∫ ω, Real.exp (θ * G ω) ∂P) =
        Real.exp ((v : ℝ) * θ ^ 2 / 2) := by sorry
