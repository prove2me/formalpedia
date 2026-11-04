-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_exact_clock_G_L1_nonpositive
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_discounted_exact_clock_G_L1_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:08:10.853535+00:00
-- url     : https://prove2.me/theorems/41008e2e-bff7-497b-9a16-27972a1f867f
-- title:
--   Discounted original exact-clock source generator drift is globally integrable and nonpositive
-- statement:
--   For the original controlled reserve and exact ruin-truncated clock, a genuine joint time×P L1 estimate of the discounted predictable generator residual transports to Integrable G P by pinned Fubini, while original-source interior HJB and strictly positive exponential discount give G≤0 almost surely. Source boundary atoms are not removed.
-- source:
--   Original source c9db7a94 for strict pre-ruin predictable interior; pinned Mathlib Integrable.integral_prod_right and integral_nonpos_of_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original discounted generator has a globally L¹, nonpositive source residual. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_discounted_exact_clock_G_L1_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (n : ℕ) (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (hL1 : Integrable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ))) * (if 0 < p.1 ∧ (p.1 : ℝ≥0∞) <
          min (ruinTime X x D p.2) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
        else 0)) (μ.prod P)) :
    Integrable (fun ω =>
      ∫ t : ℝ≥0,
        Real.exp (-(q * (t : ℝ))) * (if 0 < t ∧ (t : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0) ∂μ) P ∧
    ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0,
        Real.exp (-(q * (t : ℝ))) * (if 0 < t ∧ (t : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0) ∂μ) ≤ 0 := by sorry
