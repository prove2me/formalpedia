-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_closedcap_physical_dividend_budget
-- name    : AvramDividend.Classical.avram_bv_correct12_finite_activity_closedcap_physical_dividend_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T01:23:12.312874+00:00
-- url     : https://prove2.me/theorems/3eadd48e-539a-4053-a0ac-9172fbe1429c
-- title:
--   Original finite-activity BV physical dividend and candidate pathwise budget including the cap
-- statement:
--   Under the original Standing BV finite-negative-activity HJB assumptions, there is a single coefficient controlling actual process right-dividend mass plus candidate-value change between any ordered times whose postpayment reserves lie in the closed band from zero through b. The assumption b is permitted to equal a finite cap C. This is a pathwise physical bound on the original probability space; it does not assert the discounted expected HJB reward.
-- source:
--   Original finite-cap strict-horizon source 8271cf4d via parent 3993433e. Combines public Proved 30b67978 (one-sided candidate Lipschitz through cap), 2ba5cc4f (full-cap secant lower bound), 221932c9 (actual stopped dividend and candidate right-limit budget). Cap equality previously missing from 4cf61f35, which required b strictly below C.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finite_activity_closedcap_physical_dividend_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
        x + X.X s ω - rightLimit D s ω ∈ Icc 0 b →
        x + X.X t ω - rightLimit D t ω ∈ Icc 0 b →
        (rightLimit D t ω - rightLimit D s ω) +
          (w (x + X.X t ω - rightLimit D t ω) -
            w (x + X.X s ω - rightLimit D s ω)) ≤
          L * (((t : ℝ) - (s : ℝ)) * X.drift) := by sorry
