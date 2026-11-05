-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_negative_exp_fourth_weighted_source_measure_ext
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_negative_exp_fourth_weighted_source_measure_ext
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:56:24.746082+00:00
-- url     : https://prove2.me/theorems/37bbb089-cd92-49e1-ac6c-ff2fd9cca452
-- title:
--   Fourth-weighted exponential images uniquely determine strictly negative Borel source measures
-- statement:
--   For arbitrary Borel measures supported almost everywhere on the strictly negative real line, equality of their fourth-weighted exponential pushforwards implies equality of the original measures on all Borel sets. The map Real.exp is a measurable embedding by the pinned Polish-space theorem, and the original fourth weight (exp y - 1)^4 is strictly positive and finite for y < 0. Map injectivity and the exact pinned Mathlib withDensity_inv_same lemma cancel both transformations. No moment determinacy, finite mass of the unweighted sources, assumed rate equality, point-process intensity or stationary marked-count hypothesis is required. This is the missing explicit Borel inverse to apply after P2-M establishes equality of weighted negative-mark images.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_negative_exp_fourth_weighted_source_measure_ext
    (μ ν : Measure ℝ)
    (hnegμ : ∀ᵐ y ∂μ, y < 0)
    (hnegν : ∀ᵐ y ∂ν, y < 0)
    (himage :
      (μ.withDensity (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp =
      (ν.withDensity (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp) :
    μ = ν := by sorry
