-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_summable_L2_step_differences_centered_limit
-- name    : AvramDividend.Classical.avram_wave7_06_original_summable_L2_step_differences_centered_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:53:34.073658+00:00
-- url     : https://prove2.me/theorems/d5f8582c-03f4-4e09-b250-5438d569f4af
-- title:
--   Summable L2 step distances yield original Lévy centred martingale limit and zero mean
-- statement:
--   If the actual original-space real L2(P) step differences of finite-band/finite-grid centred martingale approximants have summable distances, their sequence is Cauchy and converges in original L2(P), preserving the zero mean of every approximation. The summability condition is an explicit sufficient tail estimate, stronger than necessary but often obtainable by selecting a rapidly decaying truncation subsequence. It avoids any separate uniform-integrability assumption because expectation is L2-continuous.
-- source:
--   W7-06 original-source quantitative tail-distance sufficient condition for small-jump L2/L1 limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_summable_L2_step_differences_centered_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSteps : Summable (fun k => dist (M k) (M (k + 1))))
    (hCentered : ∀ k, (∫ ω, M k ω ∂P) = 0) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by sorry
