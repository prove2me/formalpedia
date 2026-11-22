-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_original_infiniteactivity_reward_given_UI_four_export_heads
-- name    : AvramDividend.Classical.avram_bridge20261122_original_infiniteactivity_reward_given_UI_four_export_heads
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:11:36.546411+00:00
-- url     : https://prove2.me/theorems/b79a2946-556e-4c96-9ae6-8e75eaa35e89
-- title:
--   Original physical infinite-activity stopped reward conditional on four proved Vitali and second-moment UI interfaces
-- statement:
--   Same original spectrally negative Lévy process with infinite activity, admissible dividend strategy, positive ruin clip, stopped terminal and discounted Stieltjes cash. Additional premises provide the full source-faithful proved UI toolkit on this very sample space: eventual L2 nonnegative lintegral limit; finite-measure UI Vitali lintegral; second moment expected convergence with and without eventual bounds. The remaining mathematical work is establishing such UI/L2 hypotheses for the actual stopped jump reward approximations and proving the physical reward bound.
-- source:
--   Connected Open 464200c8 plus four remote-Proved original UI source heads 6d3dbf49,2e851383,5a31bee7,ed25acc3, including all original source dependencies.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_bridge20261122_original_infiniteactivity_reward_given_UI_four_export_heads
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hInfinite : X.ν (Iio (0 : ℝ)) = ⊤) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P)
    (hTrueJumpUI : (∀ (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (B R : ℝ≥0) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hB : ∀ n, N ≤ n → eLpNorm (Y n) 2 μ ≤ (B : ENNReal))
    (hMass : (μ Set.univ) ^ (1 / 2 : ℝ) ≤ (R : ENNReal))
    (hNonneg : ∀ n ω, 0 ≤ Y n ω)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))),
Integrable Z μ ∧ (0 ≤ᵐ[μ] Z) ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ)
        atTop (nhds (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ))) ∧
      (∀ (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hUI : UniformIntegrable Y 1 μ)
    (hNonneg : ∀ n ω, 0 ≤ Y n ω)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))),
Integrable Z μ ∧ (0 ≤ᵐ[μ] Z) ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ)
        atTop (nhds (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ))) ∧
      (∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (C : ℝ) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hi : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hC : 0 ≤ C)
    (hbound : ∀ n, N ≤ n → (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ C)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))),
Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ))) ∧
      (∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (C : ℝ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hi : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hC : 0 ≤ C)
    (hbound : ∀ n, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ C)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))),
Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)))) :
    MeasurableSet {ω : Ω | τ ω ≠ 0} ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    (∫ ω in {η : Ω | τ η ≠ 0}, Term ω + Cash ω ∂P) ≤
      w x * (P {η : Ω | τ η ≠ 0}).toReal := by sorry
