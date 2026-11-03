-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat05_ubv_positive_initial_uniform_ruin_clock_budget
-- name    : AvramDividend.Classical.avram_wave6_chat05_ubv_positive_initial_uniform_ruin_clock_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T10:59:43.325877+00:00
-- url     : https://prove2.me/theorems/3c9532b7-1071-4d95-b7a6-9279a240132f
-- title:
--   Source UBV HJB expected dividend bound at every genuine bounded ruin clock
-- statement:
--   For positive initial capital and cap, the genuine corrected UBV source HJB hypotheses imply the complete discounted Stieltjes dividend cash inequality at each actual bounded ruin clock min(ruinTime,n), retaining the original paymentTimes restriction and time-zero atom. This is the precise remaining localised controlled Ito-Meyer martingale budget. The separately Proved theorem avram_wave5_05_corrected_ubv_from_actual_bounded_ruin_budgets passes uniformly from these clocks to the full finite horizon by monotone real-clock localisation, eliminating any need to reproove Fatou or Stieltjes endpoint convergence.
-- source:
--   Faithful exact hBudget obligation in Proved theorem 6e13657c-45a7-4307-8679-a8da3e3801f8, under canonical corrected UBV positive-initial child 5dfefcd2-8b97-415b-aebd-4ad77dcd29cb. It reduces the remaining stochastic proof to finite bounded source martingale localisation, not a hypothetical independent model or bound. The child remains Open and must be formally proved before the positive-reserve and canonical parents close.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat05_ubv_positive_initial_uniform_ruin_clock_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by sorry
