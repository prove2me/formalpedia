-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b0dd16_finite_activity_masked_generator_L1
-- name    : AvramDividend.Classical.avram_b0dd16_finite_activity_masked_generator_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T16:56:54.160923+00:00
-- url     : https://prove2.me/theorems/c75afa3b-670e-4b94-aa49-297d8a3c1901
-- title:
--   Finite negative-jump activity transfers original sampled candidate integrability to masked HJB generator residual
-- statement:
--   On a finite-activity BV Levy source, the original discounted HJB residual is sandwiched between zero and the negative jump-rate-and-discount multiple of a nonnegative candidate. Consequently any measurable mask of the generator residual is integrable when the masked candidate is sampled from an integrable source. This deterministic transfer is the precise missing original finite-activity HJB grid-cell L1 interface.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b0dd16_finite_activity_masked_generator_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (hW : ∀ z : ℝ, 0 ≤ w z)
    (hDrift : 0 ≤ X.drift)
    (Y : Ω → ℝ) (mask : Ω → Prop)
    (hYI : Integrable (fun ω => w (Y ω)) P)
    (hInside : ∀ ω, mask ω →
      X.GeneratorIntegrable w (Y ω) ∧
        X.generator w (Y ω) - q * w (Y ω) ≤ 0 ∧
        0 ≤ deriv w (Y ω))
    (hMeas : AEStronglyMeasurable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P) :
    Integrable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P := by sorry
