-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gtop19_original_strict_stopped_rewards_global_meas
-- name    : AvramDividend.Classical.avram_gtop19_original_strict_stopped_rewards_global_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:32:24.015998+00:00
-- url     : https://prove2.me/theorems/2d275ef9-02e9-4e47-82ca-82a3590cf168
-- title:
--   Original zero-jump strict stopped rewards are globally measurable at every true compact clock
-- statement:
--   Necessary source-exact measurability half of Open 7fe189ee and original Open 61cdc38d. Show global measurability at each genuine stopped clock, including the original prepayment riskProcess and strict paymentTimes intersect Iio random clock Stieltjes integral, and almost-everywhere strong measurability at sigma. The latter follows from Proved d9020a5d and bounded physical clock; the former needs the original s-finite dividendMeasure kernel and joint riskProcess measurability. No changed payoff or measurable representative substitution.
-- source:
--   One of two necessary reduction children of 7fe189ee-8de1-4615-880e-1526b03cde5b, which itself is root-connected child of 61cdc38d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gtop19_original_strict_stopped_rewards_global_meas
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
    (hρle : ∀ j ω, ρ j ω ≤ σ ω) :
    let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
      if ζ ω = 0 then w x else
        Real.exp (-(q * (ζ ω : ℝ))) *
          w (riskProcess X x D (ζ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    (∀ j, Measurable (H (ρ j))) ∧ AEStronglyMeasurable (H σ) P := by sorry
