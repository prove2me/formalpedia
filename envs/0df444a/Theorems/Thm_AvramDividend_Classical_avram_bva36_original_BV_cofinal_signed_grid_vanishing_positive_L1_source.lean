-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva36_original_BV_cofinal_signed_grid_vanishing_positive_L1_source
-- name    : AvramDividend.Classical.avram_bva36_original_BV_cofinal_signed_grid_vanishing_positive_L1_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T10:59:54.4112+00:00
-- url     : https://prove2.me/theorems/9f69bc5a-9806-4e63-8a55-0ef9bbc76db0
-- title:
--   Original infinite-activity BV cofinal physical signed grid with vanishing positive L1 error
-- statement:
--   On the same original Lévy process X, filtration, P and arbitrary admissible singular dividend D, construct one cofinal sequence of compensated jump gains J_m, predictable signed generator/Stieltjes drifts B_m and positive localisation errors R_m. Require integrable J_m of mean zero, integrable B_m of nonpositive mean, integrable nonnegative R_m with E[R_m] tending to zero, and pathwise original strict-inner cash plus surviving full-T postpayment reward F_m <= w(x)+J_m+B_m+R_m. Retain zero-time right dividend payments, ruin-straddling, original negative-mark measure, and infinite small-jump activity.
-- source:
--   Cofinal-grid physical source reduction of bva34; uses independently Proved bva35 monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva36_original_BV_cofinal_signed_grid_vanishing_positive_L1_source
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
    ∃ J B R : ℕ → Ω → ℝ,
      (∀ m, Integrable (J m) P ∧ (∫ ω, J m ω ∂P) = 0) ∧
      (∀ m, Integrable (B m) P ∧ (∫ ω, B m ω ∂P) ≤ 0) ∧
      (∀ m, Integrable (R m) P ∧ ∀ᵐ ω ∂P, 0 ≤ R m ω) ∧
      Tendsto (fun m => ∫ ω, R m ω ∂P) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m, ∀ᵐ ω ∂P,
        F m ω ≤ w x + (J m ω + B m ω) + R m ω) := by sorry
