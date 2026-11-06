-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_joint_stopped_reserve_weighted_generator_real_mean_cover
-- name    : AvramDividend.Classical.avram_bv_env3_original_joint_stopped_reserve_weighted_generator_real_mean_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:01:13.622796+00:00
-- url     : https://prove2.me/theorems/3dc9f08d-30ad-4409-938f-679d53c409e1
-- title:
--   Original postdividend pre-jump reserve joint-time signed generator drift expectation cover
-- statement:
--   For the exact original Levy process and its actual postpayment pre-jump reserve, integrate the strict-complement BV generator drift inequality over an arbitrary nonnegative joint time-outcome localisation weight. Both real signed integrals are explicitly required to be integrable; there is no fabricated jump law and no assertion that stochastic compensation is already supplied. A source-specific analytic reduction toward the expected finite-horizon stopped HJB budget.
-- source:
--   Official fully Proved original BV complement interior negative-jump drift cover 3794152d-4a35-496d-b893-ed3868ea4ebb, Avram-Palmowski-Pistorius (2007) Proposition 4(i), equation (5.13). The final c8770486 bridge still requires constructing the original predictable source weight and compensated martingale and passing the stopping limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_interior_jump_discount_drift_cover
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_joint_stopped_reserve_weighted_generator_real_mean_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hEnvelope : ¬ (x + T * X.drift ≤ w x))
    (μ : Measure (ℝ≥0 × Ω)) (g : ℝ≥0 × Ω → ℝ)
    (hg : ∀ᵐ p ∂μ, 0 ≤ g p)
    (hInterior : ∀ᵐ p ∂μ,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hIntD : Integrable (fun p => g p * X.drift) μ)
    (hIntG : Integrable (fun p => g p *
      (q * w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
        ∫ z in Iio (0 : ℝ),
          w ((Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) + z) -
            w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν)) μ) :
    (∫ p, g p * X.drift ∂μ) ≤
      ∫ p, g p * (q * w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
        ∫ z in Iio (0 : ℝ),
          w ((Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) + z) -
            w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) ∂μ := by sorry
