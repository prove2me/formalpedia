-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
-- name    : AvramDividend.Classical.avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T08:52:53.426688+00:00
-- url     : https://prove2.me/theorems/be84b270-f754-436d-89db-61cacfcc0bc0
-- title:
--   Infinite-activity original process physical stochastic compensation with mean-small positive error
-- statement:
--   Construct on original Lévy process X, filtration, probability P and singular dividend strategy D a zero-mean integrable compensated negative-jump gain J, a nonpositive-mean integrable predictable HJB/Stieltjes drift B, and a nonnegative integrable original-path residual R of expectation at most epsilon. Show the original strict inner cash and full surviving T reward is bounded pathwise by w(x)+J+B+R. Payoff integrability follows separately from Proved strict-cash/terminal L1 lemma and is deliberately excluded from this stochastic source obligation.
-- source:
--   Core stochastic source after removing already-proved original payoff integrability

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
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
    ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ J B R : Ω → ℝ,
        Integrable J P ∧ Integrable B P ∧ Integrable R P ∧
        (∫ ω, J ω ∂P) = 0 ∧
        (∫ ω, B ω ∂P) ≤ 0 ∧
        (∀ᵐ ω ∂P, 0 ≤ R ω) ∧
        (∫ ω, R ω ∂P) ≤ ε ∧
        (∀ᵐ ω ∂P, F n ω ≤ w x + (J ω + B ω) + R ω) := by sorry
