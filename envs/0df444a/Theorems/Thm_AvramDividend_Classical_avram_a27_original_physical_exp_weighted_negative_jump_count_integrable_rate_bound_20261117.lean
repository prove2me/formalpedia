-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:30:12.051384+00:00
-- url     : https://prove2.me/theorems/783d64bc-a7d5-46cf-a74e-84ccb745ba50
-- title:
--   Original physical negative-jump count weighted by its exponential jump-sum is integrable and bounded by Lévy intensity
-- statement:
--   For the actual original finite-activity spectrally negative Lévy path and nonnegative exponential tilt, the weighted physical negative-jump count K exp(theta J) is integrable and its expectation is nonnegative and at most t nu((-infinity,0)). This is an original-probability-space domination needed for the marked Campbell/Mecke product-compensator limit.
-- source:
--   Proved source physical negative-Borel-count exact first moment (b24) and the actual original physical jump exponential unit bound (40973). No new source space, IID mark construction or circular imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original physical negative-jump exponential weighted count is integrable and dominated by its Lévy intensity. -/

theorem AvramDividend.Classical.avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    Integrable (fun ω => (K ω : ℝ) * Real.exp (θ * J ω)) P ∧
      0 ≤ (∫ ω, (K ω : ℝ) * Real.exp (θ * J ω) ∂P) ∧
      (∫ ω, (K ω : ℝ) * Real.exp (θ * J ω) ∂P) ≤
        (((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) := by sorry
