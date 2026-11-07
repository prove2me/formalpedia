-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_masked_original_stopped_reward_regular
-- name    : AvramDividend.Classical.avram_ubv_loc6_masked_original_stopped_reward_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:42:23.641929+00:00
-- url     : https://prove2.me/theorems/27f14e91-0dc6-4111-9d7e-fdb19faee51a
-- title:
--   Original stopped UBV physical reward is measurable and nonnegative after its exact zero-clock mask
-- statement:
--   For the original unbounded-variation spectrally negative Levy process and admissible capped dividend strategy, and any right-continuous stopping time, the exact discounted post-right-payment reserve-value plus closed Iic dividendMeasure cash is nonnegative. If that exact physical payoff is integrable, its event-of-zero-clock mask by the initial HJB value is almost-everywhere strongly measurable and nonnegative; the initial HJB value itself is nonnegative. This result retains time-zero payment, ruin, horizon and cap conventions without a finite underlying measure assumption.
-- source:
--   UBV-LOC6 reduction of positive-clock physical Ito-Meyer witness 6b50f324: separates initial-value, zero-clock stopping-event measurability, original exact closed-Iic payoff and nonnegativity from the independent stopped martingale/source budget. Proved dependencies c5c9e4bf and 5893451b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_loc6_masked_original_stopped_reward_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P) :
    0 ≤ w x ∧
      AEStronglyMeasurable (fun ω => if σ ω = 0 then w x else F ω) P ∧
      (0 ≤ᵐ[P] fun ω => if σ ω = 0 then w x else F ω) := by sorry
