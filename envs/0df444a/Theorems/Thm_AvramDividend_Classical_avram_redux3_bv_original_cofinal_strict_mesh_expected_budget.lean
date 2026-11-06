-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
-- name    : AvramDividend.Classical.avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-05T23:42:48.924759+00:00
-- url     : https://prove2.me/theorems/b39f2dd1-a0f9-4ce6-a727-63d409eb3972
-- title:
--   Original BV strictly cofinal finite-grid stopped HJB expected-budget source
-- statement:
--   For the actual BV spectrally negative Lévy process and original admissible dividends, construct strictly pre-horizon increasing physical observation clocks cofinal below T. At each clock, establish the genuine original stopped discounted Stieltjes cash plus the fixed full-horizon surviving terminal expected upper bound by w(x). This is the missing finite-grid source HJB/compensator estimate; the separately proved cofinal Stieltjes bridge yields the canonical expected budget. All cap, ruin and time-zero conventions are retained without proxy processes or downstream imports.
-- source:
--   Exact a19d8b28 source and Proved 28343e2d cofinal bridge. Repaired authoring parse of stopped real clock using explicit let S : ℝ≥0. The source expected estimate remains an Open mathematical obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∃ u : ℕ → ℝ,
      Monotone u ∧
      (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      (∀ n,
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ∂P) ≤ w x) := by sorry
