-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward15_original_zero_normalised_stopped_reward_upper
-- name    : AvramDividend.Classical.avram_pj_reward15_original_zero_normalised_stopped_reward_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T12:40:27.358444+00:00
-- url     : https://prove2.me/theorems/8d851948-37a3-4050-86e1-401604ca1ad2
-- title:
--   Original bounded stopped pure-jump reward with zero-clock normalization
-- statement:
--   For the original sigma-zero infinite-variation spectrally negative Levy process and an admissible dividend strategy, at any original right-continuous stopping clock bounded by ruin and the finite horizon, the integrable physical discounted terminal plus strictly pre-ruin closed cash reward is bounded in expectation by w(x), with its value deliberately normalised to w(x) when the clock is exactly zero. This source-exact unconditional certificate yields the initial-event positive-clock budget by masking the stopping time on an initial event, preserving the time-zero right-payment atom without invalid subtraction.
-- source:
--   Genuine selected-route source reduction for 0b1a879a-c9c5-4d2c-9039-a143ec7db5dc; replaces conditional initial-event inequality with an unconditional original stopped source budget normalised to w(x) on the zero-clock event. The parent bridge uses initial-event clock masking and the exact physical reward algebra; neither original time-zero cash nor ruin/horizon atoms are discarded. Missing proof is the original same-clock pure-jump Ito-Meyer/HJB source inequality and sigma-zero smalljump passage.

import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward15_original_zero_normalised_stopped_reward_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) :
    let G : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
            else riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    Integrable G P →
      (∫ ω, G ω ∂P) ≤ w x := by sorry
