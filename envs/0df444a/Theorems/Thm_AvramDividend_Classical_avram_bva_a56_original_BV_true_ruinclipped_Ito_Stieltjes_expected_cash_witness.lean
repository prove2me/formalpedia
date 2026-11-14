-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a56_original_BV_true_ruinclipped_Ito_Stieltjes_expected_cash_witness
-- name    : AvramDividend.Classical.avram_bva_a56_original_BV_true_ruinclipped_Ito_Stieltjes_expected_cash_witness
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T16:13:26.530577+00:00
-- url     : https://prove2.me/theorems/5cfe62de-94fd-4554-9c94-b69e6c5d5f23
-- title:
--   Original BV source stopped Ito Stieltjes compensated cash witness at exact ruin-clipped clock
-- statement:
--   For every original standing infinite negative-activity BV spectrally negative Levy process, every original admissible dividend strategy and each original strict pre-T physical cash row with full T surviving postpayment candidate, at the genuine stopped clock min(T, original ruin) construct the ORIGINAL ruin-clipped pathwise Ito-Stieltjes compensator witness. It consists of actual terminal reserve and dividendMeasure inclusive clipped cash, integrable compensated negative-jump martingale M of exactly zero mean, signed HJB plus dividend correction G,H with nonpositive total almost surely, and an almost-sure source Ito upper inequality bounding the actual row reward by Term+Cash and Term+Cash by initial candidate plus martingale and corrections. This is the missing source calculus needed for expected BV parent; retain upper-cap dividend occupation, w(0) >= 0 and ruin crossing. Unlike A22 it uses no arbitrary strict interior spatial masks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a56_original_BV_true_ruinclipped_Ito_Stieltjes_expected_cash_witness
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
        (∀ᵐ ω ∂P, F n ω ≤ Term ω + Cash ω) := by sorry
