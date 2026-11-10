-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gtop18_original_strict_reward_cofinal_meas_limit
-- name    : AvramDividend.Classical.avram_gtop18_original_strict_reward_cofinal_meas_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:21:04.783195+00:00
-- url     : https://prove2.me/theorems/7fe189ee-8de1-4615-880e-1526b03cde5b
-- title:
--   Exact original zero-jump strict reward is measurable and converges along monotone cofinal stopping clocks
-- statement:
--   Necessary source-exact endpoint child of Open 61cdc38d: for any genuine monotone stopping clocks below sigma converging almost surely to sigma, prove global measurability of each exact zero-clock-masked strict Stieltjes reward, almost-sure measurability at sigma and ENNReal.ofReal reward convergence. Crucial endpoint cases are sigma zero, eventual equality, strict approach from below, positive ruin and terminal right payments. The strict Iio cash excludes any atom at the terminal time.
-- source:
--   Root-connected exact reduction of Open 61cdc38d-6371-4c61-b8e6-704e38c04057. Reuse Proved 2151ad9a left endpoint reward, d9020a5d integrability and original strict cash measurability. The sibling supplies the concrete clocks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gtop18_original_strict_reward_cofinal_meas_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
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
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω)
    (ρ : ℕ → Ω → ℝ≥0)
    (hρstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ j ω : WithTop ℝ≥0)))
    (hρle : ∀ j ω, ρ j ω ≤ σ ω)
    (hρmono : ∀ ω, Monotone (fun j : ℕ => ρ j ω))
    (hρlim : ∀ᵐ ω ∂P, Tendsto (fun j => ρ j ω) atTop (nhds (σ ω))) :
    let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
      if ζ ω = 0 then w x else
        Real.exp (-(q * (ζ ω : ℝ))) *
          w (riskProcess X x D (ζ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    (∀ j, Measurable (H (ρ j))) ∧
    AEStronglyMeasurable (H σ) P ∧
    (∀ᵐ ω ∂P, Tendsto
      (fun j => ENNReal.ofReal (H (ρ j) ω)) atTop
      (nhds (ENNReal.ofReal (H σ ω)))) := by sorry
