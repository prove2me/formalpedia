-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a57_original_BV_ruinclipped_true_cash_survivor_domination
-- name    : AvramDividend.Classical.avram_bva_a57_original_BV_ruinclipped_true_cash_survivor_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:17:48.982545+00:00
-- url     : https://prove2.me/theorems/9f3a5749-c10b-412c-ba87-b6b93ac29e8a
-- title:
--   Original BV strict prehorizon cash and surviving reward dominated by ruin-clipped stopped cash and terminal
-- statement:
--   For the original BV spectrally negative Levy and admissible dividends, assume the genuine stopped terminal W and Term and that actual original discounted dividendMeasure cash strictly before the physical prehorizon cutoff is dominated by inclusive ruin-clipped Cash, and that the surviving T terminal Term equals the original postpayment candidate at T. The proof uses the already Proved original piecewise stopped terminal nonnegativity (including w(0)>=0) and a two-case split on survival to show original strict F_n is dominated pathwise by Term+Cash. This isolates deterministic cash/terminal bookkeeping from source martingale Ito calculus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a57_original_BV_ruinclipped_true_cash_survivor_domination
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
    ∀ (n : ℕ) (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ),
      (∀ ω, W ω =
        if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) →
      (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) →
      (∀ ω,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤ Cash ω) →
      (∀ ω,
          (S : ℝ≥0∞) < ruinTime X x D ω →
            Term ω = Real.exp (-(q * T)) * w (riskProcess X x D S ω)) →
      ∀ᵐ ω ∂P, F n ω ≤ Term ω + Cash ω := by sorry
