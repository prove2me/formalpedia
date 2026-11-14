-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a58_original_BV_ruinclipped_Ito_Stieltjes_true_source_components
-- name    : AvramDividend.Classical.avram_bva_a58_original_BV_ruinclipped_Ito_Stieltjes_true_source_components
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T16:17:54.140344+00:00
-- url     : https://prove2.me/theorems/3e22fef7-1125-4f71-9039-3a99e0feb5d1
-- title:
--   Original BV exact ruin-clipped Ito Stieltjes signed martingale source with cash covering and surviving terminal identity
-- statement:
--   At the original exact stopped clock min(T,ruin), for each physical grid index construct actual original stopped cash/terminal, integrable centred full negative-jump compensator M, signed HJB+dividend G,H with nonpositive sum and source discounted stopped Ito upper inequality. Retain upper-cap dividend occupation, zero reserve w(0)>=0, and original X,D, and separately certify original strict prehorizon cash inclusion in clipped cash and the full-horizon surviving terminal equality. This is the actual missing source-level stochastic calculus, enough to derive the A56 witness using A57 bookkeeping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a58_original_BV_ruinclipped_Ito_Stieltjes_true_source_components
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
    ∀ n : ℕ, ∃ (τ : Ω → ℝ≥0),
      (∀ ω, τ ω = (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal) ∧
      (∀ ω, τ ω ≤ S) ∧
      IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω) ∧
      ∃ (W Cash Term M G H : Ω → ℝ),
        (∀ ω, W ω =
          if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) ∧
        (∀ ω, Cash ω =
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
        (∀ ω, Term ω =
          Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
        Integrable Term P ∧ Integrable Cash P ∧ Integrable M P ∧
        Integrable G P ∧ Integrable H P ∧
        (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
        (∀ᵐ ω ∂P, Term ω + Cash ω ≤
          w x + M ω + G ω + H ω) ∧
        (∀ ω,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤ Cash ω) ∧
        (∀ ω,
          (S : ℝ≥0∞) < ruinTime X x D ω →
            Term ω = Real.exp (-(q * T)) * w (riskProcess X x D S ω)) := by sorry
