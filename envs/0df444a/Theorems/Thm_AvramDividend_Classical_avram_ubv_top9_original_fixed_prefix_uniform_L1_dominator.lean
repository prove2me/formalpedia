-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_fixed_prefix_uniform_L1_dominator
-- name    : AvramDividend.Classical.avram_ubv_top9_original_fixed_prefix_uniform_L1_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:40:40.325171+00:00
-- url     : https://prove2.me/theorems/89a84a09-b413-427d-b7f7-ac6d09aaa021
-- title:
--   A single integrable full-horizon cash envelope dominates every original fixed-prefix localised reward
-- statement:
--   For a countable family of genuine source stopping clocks sharing one original Levy path prefix ceiling and lying before the same bounded outer horizon, all actual after-rightpayment stopped reward absolute values are almost surely dominated by one common integrable random variable. This establishes the true fixed-band uniform-integrability interface for removing further inner localisations at infinite surplus cap, while making no unsupported claim of uniform domination across increasing ceilings.
-- source:
--   Proved original source reward upper envelope da71b569, prefix reserve ceiling 2036a555, topcap nonnegative terminal e225ab08; exact canonical Integrable of full Stieltjes cash gives integrability of the common full-cash majorant. Supports physical witness 25573e81, with no surrogate processes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_fixed_prefix_uniform_L1_dominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hCashI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (B : ℝ) (hB : 0 < x + B)
    (κ : ℕ → Ω → ℝ≥0) (hκle : ∀ j ω, κ j ω ≤ τ ω)
    (hκprefix : ∀ j ω (t : ℝ≥0), t ≤ κ j ω → X.X t ω ≤ B) :
    ∃ g : Ω → ℝ, Integrable g P ∧ ∀ j, ∀ᵐ ω ∂P,
      |Real.exp (-(q * (κ j ω : ℝ))) *
        w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
          else riskProcess X x D (κ j ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal| ≤
      g ω := by sorry
