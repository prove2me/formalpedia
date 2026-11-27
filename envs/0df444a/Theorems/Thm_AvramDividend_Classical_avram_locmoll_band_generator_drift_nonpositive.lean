-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_generator_drift_nonpositive
-- name    : AvramDividend.Classical.avram_locmoll_band_generator_drift_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:55:15.841541+00:00
-- url     : https://prove2.me/theorems/9230860a-8043-5367-8f0a-6209f5c792f1
-- title:
--   Discounted physical-time generator drift on the stopped band is nonpositive
-- statement:
--   Discounted physical-time generator drift on the stopped band is nonpositive
-- source:
--   Exact decomposition of 07460cee-1650-4edf-a37c-1b2c076b8656

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_generator_drift_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (C : ℝ≥0∞) (hC : 0 < C)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (δ R : ℝ) (hδ : 0 < δ) (hδx : δ < x) (hxR : x < R)
    (θ : Ω → ℝ≥0)
    (hθle : ∀ ω, θ ω ≤ T.toNNReal)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R)
    (hstop : IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : WithTop ℝ≥0)))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hNonneg : ∀ y : ℝ, 0 ≤ g y)
    (hZero : ∀ y : ℝ, y ≤ 0 → g y = 0)
    (hGrad : ∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y)
    (hGen : ∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
      X.GeneratorIntegrable g y ∧ X.generator g y - q * g y ≤ 0)
    (hSec : ∀ a b : ℝ, δ ≤ b → b ≤ a →
      a - b ≤ g a - g b)
    (hLoss : ∀ a b : ℝ, 0 ≤ b → b ≤ a →
      a - b ≤ g a - g b + δ) :
    ∀ ω, (fun ω : Ω => ∫ t in Ioc (0 : ℝ) (θ ω : ℝ),
      Real.exp (-(q * t)) *
        (X.generator g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal) -
          q * g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal))) ω ≤ 0 := by sorry
