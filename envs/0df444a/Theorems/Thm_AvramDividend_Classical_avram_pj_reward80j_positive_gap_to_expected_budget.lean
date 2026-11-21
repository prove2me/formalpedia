-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward80j_positive_gap_to_expected_budget
-- name    : AvramDividend.Classical.avram_pj_reward80j_positive_gap_to_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:04:12.398332+00:00
-- url     : https://prove2.me/theorems/d9235991-52c0-4d7f-9bb9-55479ad44b7b
-- title:
--   Vanishing positive original stopped reward excess and nonpositive compensated HJB mean imply exact expectation upper budget
-- statement:
--   For a genuine probability measure, an integrable stopped reward G, an integrable compensated generator/jump process H of nonpositive mean and arbitrarily small expected positive gap G-(a+H) force the exact stopped reward expectation to be at most its HJB initial budget a. This isolates the final deterministic mean argument while preserving the signed compensated source.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward80j_positive_gap_to_expected_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (G H : Ω → ℝ)
    (hGI : Integrable G P)
    (hHI : Integrable H P)
    (hHmean : (∫ ω, H ω ∂P) ≤ 0)
    (hGap : ∀ ε : ℝ, 0 < ε →
      (∫ ω, max (0 : ℝ) (G ω - (a + H ω)) ∂P) ≤ ε) :
    (∫ ω, G ω ∂P) ≤ a := by sorry
