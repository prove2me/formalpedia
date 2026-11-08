-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn52_origin_value_positive_of_BV_HJB
-- name    : AvramDividend.Classical.avram_bv_env3_turn52_origin_value_positive_of_BV_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:06:32.76995+00:00
-- url     : https://prove2.me/theorems/92e61d41-6f62-41fd-9b57-494e7a768c2c
-- title:
--   Strict positive HJB boundary value at zero for original positive-drift bounded-variation Levy generator
-- statement:
--   The original BV HJB supersolution must have a strictly positive right boundary value at zero if the original process has strictly positive drift. Assume w(0)=0 and integrate its exact generator inequality over a shrinking positive interval. The BV truncated negative-jump first moment tends to zero, while the positive drift remains fixed and the derivative lower bound forces a strictly positive linear increase, giving a contradiction.
-- source:
--   Original BV generator and Levy measure, positive drift, finite negative-jump first variation, HJB and C1 derivative lower bound. This isolates the genuine sole zero-reserve analytical obstruction after positive reserves have already been solved by Proved 6da04f9a. No dividend process, Fatou grid or HJB assumption was added.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn52_origin_value_positive_of_BV_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hDrift : 0 < X.drift) :
    0 < w 0 := by sorry
