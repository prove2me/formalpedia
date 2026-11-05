-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
-- name    : AvramDividend.Classical.avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:05:21.791337+00:00
-- url     : https://prove2.me/theorems/1fba8396-2264-4f16-a8c0-e13df4ae4bac
-- title:
--   Original canonical dividend HJB jump inequality from C1 closed-cap secants without Standing or BV
-- statement:
--   For any admissible original spectrally negative Levy source, the positive-cap C1 gradient inequality alone controls each genuine right dividend atom at time zero or strictly before ruin. The original source physical cap condition and zero initial fields give exact closed-cap contact even when the ruin clock is zero. This strictly weakens source hypotheses of previously Proved canonical hjump helper by dropping Standing, BV and nonnegative initial reserve assumptions.
-- source:
--   Proved original source dividendStrategy_le_rightLimit and closed-cap secant aeec073e, with IsAdmissibleLe physical solvency, cap and initial fields; no import of Open P3 residual.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by sorry
