-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a68_original_BV_strict_prehorizon_eventual_lower
-- name    : AvramDividend.Classical.avram_bva_a68_original_BV_strict_prehorizon_eventual_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:07:30.357277+00:00
-- url     : https://prove2.me/theorems/878675b0-f34d-4496-8317-a2f811957dcf
-- title:
--   Original stopped strictly prehorizon dividend cash and prepayment surviving terminal eventually bound fixed inner F from below
-- statement:
--   For the original BV infinite negative activity dividend setup, the actual killed reward at clocks r_m=T−T/(m+2), containing strictly before r_m dividends and the prepayment terminal at r_m, eventually exceeds the original cash F_n with its full-horizon prepayment terminal to within any positive epsilon. Uses physical prefix monotonicity, finite original discounted Stieltjes cash, and the Proved original killed-terminal left-limit lower theorem. This is the genuine no-postpayment-mismatch analytic obligation for A63.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a68_original_BV_strict_prehorizon_eventual_lower
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
    let r : ℕ → ℝ≥0 := fun n => Real.toNNReal (T - δ n)
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let G : ℕ → Ω → ℝ := fun n ω =>
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (r n : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (r n : ℝ))) * w (riskProcess X x D (r n) ω) else 0))
    ∀ n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in atTop, F n ω - ε < G m ω := by sorry
