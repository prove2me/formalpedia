-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_uniform_fullcap_candidate_lipschitz
-- name    : AvramDividend.Classical.avram_bv_correct12_finite_activity_uniform_fullcap_candidate_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:24:28.104985+00:00
-- url     : https://prove2.me/theorems/30b67978-403b-40df-8fa7-0e2650e4d0db
-- title:
--   Finite-activity BV candidate one-sided Lipschitz bound includes positive-cap contact
-- statement:
--   On the original Standing bounded-variation finite-negative-activity Levy process, the same positive-cap HJB and continuous candidate premises imply a one-sided Lipschitz coefficient on the entire compact nonnegative band through the cap endpoint, including reserve zero and the exact finite cap. The derivative bound applies strictly inside the cap; the endpoint limit uses continuity and strict monotonicity of ENNReal.ofReal on positive arguments.
-- source:
--   Strengthens Proved 75b9a7d6 from strict b<C to inclusive b≤C, using Proved 9db99eb1 uniform derivative ceiling and cap-endpoint continuity. Source-exact boundary/positive-cap contact interface for 8271cf4d then 3993433e→73419313→51b72610.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finite_activity_uniform_fullcap_candidate_lipschitz
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
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ b →
        w t - w s ≤ L * (t - s) := by sorry
