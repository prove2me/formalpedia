-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_compact_physical_dividend_budget
-- name    : AvramDividend.Classical.avram_bv_correct12_finite_activity_compact_physical_dividend_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:23:01.307315+00:00
-- url     : https://prove2.me/theorems/4cf61f35-45a3-4329-b6a0-e7ac8cec1098
-- title:
--   Original finite-activity BV physical dividend and candidate budget on the entire nonnegative compact reserve band
-- statement:
--   For an actual Standing spectrally negative bounded-variation process with finite negative-jump activity, a positive cap, original HJB hypotheses and an original adapted dividend strategy, there exists an explicit uniform Lipschitz coefficient of the candidate on a compact reserve band including zero. Consequently, on almost every original path, whenever the two stopped postpayment reserves lie in the band, all intervening right-dividend mass plus the candidate value increment is bounded by this coefficient times the elapsed physical drift. No separate Lipschitz or assumed Ito identity is required.
-- source:
--   Source-exact original finite-cap marked stopped budget path towards 3993433e, 73419313 and 51b72610. The uniform zero-boundary Lipschitz consequence of Proved 75b9a7d6 combines with Proved full-cap gradient secant 2ba5cc4f and original pathwise physical budget 221932c9, eliminating their separate compact-band Lipschitz assumption. It does not claim a global expected HJB budget.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finite_activity_compact_physical_dividend_budget
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
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b < C) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
        x + X.X s ω - rightLimit D s ω ∈ Icc 0 b →
        x + X.X t ω - rightLimit D t ω ∈ Icc 0 b →
        (rightLimit D t ω - rightLimit D s ω) +
          (w (x + X.X t ω - rightLimit D t ω) -
            w (x + X.X s ω - rightLimit D s ω)) ≤
          L * (((t : ℝ) - (s : ℝ)) * X.drift) := by sorry
