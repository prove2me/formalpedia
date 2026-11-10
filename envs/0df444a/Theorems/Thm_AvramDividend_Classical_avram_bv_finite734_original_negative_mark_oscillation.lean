-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_finite734_original_negative_mark_oscillation
-- name    : AvramDividend.Classical.avram_bv_finite734_original_negative_mark_oscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:37:40.054599+00:00
-- url     : https://prove2.me/theorems/e0a98361-b476-4598-bc55-ec4ce031a327
-- title:
--   Original finite-activity negative-jump value increment uniformly bounded on a closed reserve band
-- statement:
--   For an original Standing bounded-variation spectrally negative Levy process with finite negative-jump activity and the exact Avram C1-HJB assumptions, on each closed reserve band [0,epsilon] inside the cap, the jump increment w(y+z)-w(y) is uniformly bounded over all negative marks z. The finite-activity compensator can therefore use a globally bounded jump kernel without a first-moment hypothesis on the jump sizes. Supports original physical stopped martingale construction for 3f849360.
-- source:
--   Root route 3f849360 -> 00e7ded9 -> stopped compensated cash error; follows Proved 73d0c52e closed-cap Lipschitz plus w=0 on negative reserves.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_finite_activity_closed_both_boundaries_HJB_lipschitz
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_finite734_original_negative_mark_oscillation
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
    (hactivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y z : ℝ, y ∈ Icc (0 : ℝ) ε → z < 0 →
        |w (y + z) - w y| ≤ K := by sorry
