-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uniform_survival_original_caplinear_budget
-- name    : AvramDividend.Classical.avram_p3_grid4_uniform_survival_original_caplinear_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:19:11.665238+00:00
-- url     : https://prove2.me/theorems/805360a7-88e4-47d9-bc80-1c09ca486383
-- title:
--   Exact original surviving BV cap-linear cash and terminal source on uniform physical grid
-- statement:
--   For the genuine original Lévy X and dividend D, with uniform physical cell endpoints and cap-linear value extension, on survival through T the actual strict discounted dividend integral over paymentTimes intersect Iio T plus pre-right-payment terminal is bounded by w x and the exact original discounted frozen-caplinear physical increments, including final horizon gap. This instantiates the Proved original surviving-source theorem facfb545, with all strict cell and horizon inequalities derived from the uniform geometry; it is a source-exact surviving branch required by the stopped Fatou physical-grid residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_surviving_strict_horizon_source_upper
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_uniform_survival_original_caplinear_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (ω : Ω)
    (hSurvive :
      ENNReal.ofReal T < ruinTime X x D ω) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u n i : ℝ)))
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω) -
      V (x + X.X (u n i) ω - rightLimit D (u n i) ω)
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) ≤
      w x + (∑ i ∈ Finset.range (n + 1), e i * source i) +
        e (n + 1) * (V (x + X.X S ω - rightLimit D (u n (n + 1)) ω) -
          V (x + X.X (u n (n + 1)) ω -
            rightLimit D (u n (n + 1)) ω)) := by sorry
