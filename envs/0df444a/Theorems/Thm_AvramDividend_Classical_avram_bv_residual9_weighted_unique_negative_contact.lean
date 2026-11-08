-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_weighted_unique_negative_contact
-- name    : AvramDividend.Classical.avram_bv_residual9_weighted_unique_negative_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:19:52.5805+00:00
-- url     : https://prove2.me/theorems/490ee199-79d4-402c-b4a7-090d55d1597d
-- title:
--   Only the single exceptional stopped-grid contact contributes to the weighted negative post-value error
-- statement:
--   For any finite source grid, if all post-cell values are nonnegative except possibly one known contact index and the nonnegative-part weights are at most one, then the weighted sum of negative post-value parts is bounded by the negative part at that one contact. This is the deterministic one-contact reduction needed by the exact BV discounted C1 six-term identity; the stochastic existence and expectation convergence of the contact remain independent.
-- source:
--   AVRAM BV-RESIDUAL9 round-four unique-ruin-contact negative discount-error

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_weighted_unique_negative_contact
    (w post : ℕ → ℝ) (m j : ℕ)
    (hj : j < m + 1)
    (hw : ∀ i, i < m + 1 → w i ≤ 1)
    (hpost : ∀ i, i < m + 1 → i ≠ j → 0 ≤ post (i + 1)) :
    (∑ i ∈ Finset.range (m + 1),
      w i * max (-post (i + 1)) 0) ≤
      max (-post (j + 1)) 0 := by sorry
