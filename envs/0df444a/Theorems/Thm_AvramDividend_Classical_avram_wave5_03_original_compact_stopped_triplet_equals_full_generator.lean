-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_compact_stopped_triplet_equals_full_generator
-- name    : AvramDividend.Classical.avram_wave5_03_original_compact_stopped_triplet_equals_full_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:35:21.508003+00:00
-- url     : https://prove2.me/theorems/3ad3e17c-05a9-40bf-8044-4d597848d702
-- title:
--   Exact same-source ruin-stopped compact Gaussian, drift and negative-jump triplet equals generator residual pointwise
-- statement:
--   On the literal original spectrally negative Levy X, admissible-control path D and its actual ruinTime, identify the inclusive-stop compact-band Gaussian curvature, source linear discounted drift and ν-integrated nonlinear negative-mark generator Taylor kernel exactly with the original source X.generator w−q w at the predictable prepayment left limit. This is the missing algebraic equality needed to transfer the jointly integrable true-clock three-component drift to the HJB nonpositive residual; it asserts no artificial process or stochastic Ito martingale identity. Applies to BV when σ=0 and UBV under C2.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), original controlled stopped Ito–Meyer generator triplet; directly uses the accepted Chat03 648e8603 genuine component L1 and the exact source original-generator definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_compact_stopped_triplet_equals_full_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (u v δ q : ℝ) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
      else 0
    let L : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.c * deriv w (Y p) - q * w (Y p)
      else 0
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ p : ℝ≥0 × Ω,
      (ρ p * G p + ρ p * L p) +
        (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) =
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0) := by sorry
