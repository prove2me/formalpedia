-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:33:58.669582+00:00
-- url     : https://prove2.me/theorems/5893451b-5c95-4460-b400-7bc3d2b67e65
-- title:
--   Exact original UBV stopped reward nonnegative at every physical clock and closed payment boundary
-- statement:
--   For the original unbounded variation spectrally negative Levy process and admissible capped or unlimited strategy, each exact physical stopped paid reward is nonnegative, with terminal w evaluated after any permitted right-limit dividend and the dividend measure integrated over paymentTimes intersect the closed Iic clock. The proof uses the already Proved original stopped terminal nonnegativity across zero/survival/ruin and positivity of the closed Stieltjes cash. No stopping-time, adaptedness, integrability or convergence is assumed.
-- source:
--   Original physical payoff sign component of fa7052b1 and of the positive-clock Ito-Meyer witness, based on Proved f6fef241 and all-cap original book-reserve bounds. Source exact at any clock, cap and time-zero dividend.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, 0 ≤ F ω := by sorry
