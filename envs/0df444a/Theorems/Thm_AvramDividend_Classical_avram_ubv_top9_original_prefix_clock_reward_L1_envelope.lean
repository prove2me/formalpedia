-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_prefix_clock_reward_L1_envelope
-- name    : AvramDividend.Classical.avram_ubv_top9_original_prefix_clock_reward_L1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:26:01.232068+00:00
-- url     : https://prove2.me/theorems/da71b569-531a-411f-b2d9-00b5ddee3239
-- title:
--   Uniform physical prefix clock discounted reward is dominated by an integrable full-cash envelope
-- statement:
--   At any source physical clock with an original Lévy path prefix ceiling, the exact discounted after-rightpayment terminal value plus closed-payment-clock cash is pointwise dominated almost surely by the candidate value at the spatial ceiling and the original full-horizon cash. The full-horizon cash is an assumed L1 observable in the canonical theorem. The domination holds simultaneously for every chosen clock using the same bounded natural horizon, with no global spatial cap or additional process.
-- source:
--   Compose source-exact Proved e225ab08 and new original prefix reserve ceiling with Proved e1455beb bounded-clock Stieltjes cash finiteness and 4e119742 closed-clock real cash monotonicity. Directly prepares L1 localisation needed for original witness 25573e81; no proof of Ito is claimed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_prefix_clock_reward_L1_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ ρ : Ω → ℝ≥0) (hρle : ∀ ω, ρ ω ≤ τ ω)
    (T : ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (B : ℝ) (hB : 0 < x + B)
    (hXprefix : ∀ ω (t : ℝ≥0), t ≤ ρ ω → X.X t ω ≤ B) :
    ∀ᵐ ω ∂P,
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      w (x + B) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
