-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a63_original_BV_strict_prehorizon_terminal_Fatou_liminf_and_measurable
-- name    : AvramDividend.Classical.avram_bva_a63_original_BV_strict_prehorizon_terminal_Fatou_liminf_and_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:51:28.890354+00:00
-- url     : https://prove2.me/theorems/ef04fd55-d4cc-4dfe-b6a1-edd3f7326b5b
-- title:
--   Original infinite-activity BV prehorizon cash and prepayment terminal Fatou liminf with measurable stopped rewards
-- statement:
--   Original true physical strict-prehorizon horizon limit bridge, independent of stochastic compensation. For the deterministic predecessor clocks r_n=T-T/(n+2), the nonnegative actual discounted cash strictly before r_n plus the true prepayment survivor reward at r_n is a measurable ENNReal random variable. Every original inner cash row with the fixed full-horizon surviving prepayment candidate is dominated almost surely by the liminf of these predecessor rewards. Use Proved left-limit terminal continuity (a9b3240d and 7420c238), discounted prefix cash monotonicity (f9673459) and positive surviving terminal h_nonneg. The result combines with source A62 and Fatou to prove the original expected A55 without the false A56 terminal equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a63_original_BV_strict_prehorizon_terminal_Fatou_liminf_and_measurable
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
    let G : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (r n : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (r n : ℝ))) * w (riskProcess X x D (r n) ω) else 0))
    (∀ n, Measurable (G n)) ∧
    ∀ n, ∀ᵐ ω ∂P,
      ENNReal.ofReal (F n ω) ≤
        liminf (fun m : ℕ => G m ω) atTop := by sorry
