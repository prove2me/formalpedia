-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva31_original_infinite_activity_centred_jump_signed_drift_eps_certificate
-- name    : AvramDividend.Classical.avram_bva31_original_infinite_activity_centred_jump_signed_drift_eps_certificate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T08:41:28.087562+00:00
-- url     : https://prove2.me/theorems/41834f26-6074-422c-a73b-9ad6bca28450
-- title:
--   Original infinite-activity BV physical source certificate: centred jump and signed predictable drift
-- statement:
--   For every original strict horizon, construct on the original X,D,P an integrable zero-mean centred jump gain J, an integrable nonpositive-mean predictable-generator and Stieltjes drift B, and an epsilon-localisation error, yielding the pathwise bound F_n <= w(x)+J+B+epsilon. Requires original negative-jump measure, infinite small-mark limit, arbitrary singular dividends, time-zero rights, common jumps, ruin and T endpoints.
-- source:
--   Physically split original-source epsilon-cash witness bcb5f5e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva31_original_infinite_activity_centred_jump_signed_drift_eps_certificate
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
      ∃ J B : Ω → ℝ,
        Integrable (F n) P ∧ Integrable J P ∧ Integrable B P ∧
        (∫ ω, J ω ∂P) = 0 ∧
        (∫ ω, B ω ∂P) ≤ 0 ∧
        (∀ᵐ ω ∂P, F n ω ≤ w x + (J ω + B ω) + ε) := by sorry
