-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_weighted_exact_candidate_enumeration
-- name    : AvramDividend.Classical.avram_bv_jump8_cadlag_weighted_exact_candidate_enumeration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-07T00:23:19.644294+00:00
-- url     : https://prove2.me/theorems/e2bed90b-591b-4274-ac67-2df0882b298f
-- title:
--   Exact weighted càdlàg intrinsic jump lintegral equals deduplicated measurable candidate series
-- statement:
--   Construct the measurable dense-grid candidate jump-time selectors and exact measurable marks, and show that for every càdlàg path the original mapped counting-measure integral of any nonnegative Borel mark weight is exactly the countable first-occurrence series, with zero marks explicitly discarded. This is the essential weighted extension of already proved Borel marked jump-count enumeration, and preserves time-zero exclusion.
-- source:
--   Use the Proved two-sign candidate-time enumeration 417d1996, measurable candidate exact mark reconstruction 660f311b, canonical left limit, and the countable first-candidate covering theorem. Unlike an unweighted count, prove the weighted lintegral-to-tseries identity through count-measure Tonelli/map and deduplicated first-appearance grouping. Needed with measurable weighted series to reduce b50e56f2 without asserting a Poisson law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_jump8_cadlag_weighted_exact_candidate_enumeration
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
      (mark : ℕ → (ℝ≥0 → ℝ) → ℝ),
      (∀ k, Measurable (time k)) ∧
      (∀ k, Measurable (mark k)) ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        (∑' k : ℕ,
          if 0 < time k Y ∧ time k Y ≤ T ∧
              (∀ j : ℕ, j < k → time j Y ≠ time k Y)
          then (if mark k Y = 0 then 0 else g (mark k Y))
          else 0) =
        ∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
            (fun u => (u, Y u - Function.leftLim Y u))) := by sorry
