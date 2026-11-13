-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva39_original_BV_physical_signed_budget_positive_excess_mean_zero_limit
-- name    : AvramDividend.Classical.avram_bva39_original_BV_physical_signed_budget_positive_excess_mean_zero_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T11:21:42.836117+00:00
-- url     : https://prove2.me/theorems/03ddb676-f2df-4cc4-9555-d3a08581a9ef
-- title:
--   Original BV infinite-activity physical signed grid with vanishing expected positive excess
-- statement:
--   Construct along one cofinal original-process strict-inner horizon grid a source-faithful integrable signed budget N_m with nonpositive expectation such that the expected positive excess of the actual Stieltjes cash plus surviving T postpayment reward above w(x)+N_m tends to zero. The integrability of this positive excess is automatic once N_m is integrable, by already Proved avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1. This leaves one quantitative L1-small physical signed-ledger obligation handling infinite small jumps, zero-time right payments and ruin contacts.
-- source:
--   Physical bottleneck after removing automatic positive-excess integrability with Proved p3_comp9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva39_original_BV_physical_signed_budget_positive_excess_mean_zero_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∃ N : ℕ → Ω → ℝ,
      (∀ m, Integrable (N m) P ∧ (∫ ω, N m ω ∂P) ≤ 0) ∧
      Tendsto (fun m =>
        ∫ ω, max (F m ω - (w x + N m ω)) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
