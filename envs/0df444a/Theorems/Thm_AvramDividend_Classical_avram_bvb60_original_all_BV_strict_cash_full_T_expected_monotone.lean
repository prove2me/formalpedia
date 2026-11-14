-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb60_original_all_BV_strict_cash_full_T_expected_monotone
-- name    : AvramDividend.Classical.avram_bvb60_original_all_BV_strict_cash_full_T_expected_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:38:31.637562+00:00
-- url     : https://prove2.me/theorems/105b2e25-8870-492b-87da-899ebe58a039
-- title:
--   All original bounded variation negative-jump activities: true-horizon strict cash expected rewards form a monotone sequence
-- statement:
--   For the exact original BV spectrally negative Levy filtered process, without a finite/infinite negative activity split, the expectations of original strictly truncated discounted dividend cash plus full T survival terminal payoff are monotone in the uniform mesh index. BVB47 gives physical source pointwise a.e. monotonicity; BVB58 proves exact source cash integrability without any negative-activity hypothesis. This supports cofinal expected-budget arguments in BVB59 and generalises BVA42.
-- source:
--   Accepted source physical cash a.e. monotonicity BVB47 and source all-BV integrability BVB58 (independent of Lévy negative activity).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb60_original_all_BV_strict_cash_full_T_expected_monotone
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
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n m : ℕ, n ≤ m →
      (∫ ω, F n ω ∂P) ≤ (∫ ω, F m ω ∂P) := by sorry
