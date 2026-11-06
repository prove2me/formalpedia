-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_ito_boundary_union_masked_expected_cash_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_ito_boundary_union_masked_expected_cash_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:15:04.70349+00:00
-- url     : https://prove2.me/theorems/73f074c9-d57b-492b-8e5f-b00ff22ecd65
-- title:
--   Original stochastic HJB budget on the disjoint union of zero-n, zero-horizon or immediate-ruin boundary paths
-- statement:
--   In the exact original source Lévy probability space, the event-masked expectation of raw discounted Stieltjes cash across all three deterministic boundary faces n=0 or T=0 or true ruinTime=0 is at most the matching event-masked initial HJB value. This single masked bound preserves probability weighting and the time-zero atom without double-counting a separate bound for each event. It leaves the strictly positive n,T,ruinTime stochastic interior explicitly open.
-- source:
--   Apply ENNReal lintegral monotonicity to the Proved/public source pointwise union-boundary certificate (must first be Proved/public). Split exact boundary event disjunction and use the pointwise original HJB cash bound on that event; outside, both integrands vanish. No P4-F3 martingale source imported; no assumption of interior budget.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_ito_boundary_union_pointwise_cash_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_ito_boundary_union_masked_expected_cash_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, if n = 0 ∨ T = 0 ∨ ruinTime X x D ω = 0 then
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, if n = 0 ∨ T = 0 ∨ ruinTime X x D ω = 0 then
      ENNReal.ofReal (w x) else 0 ∂P) := by sorry
