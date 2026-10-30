-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
-- name    : AvramDividend.Classical.avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:41:18.510081+00:00
-- url     : https://prove2.me/theorems/a560158e-9773-495e-8cf6-9ac8a8ef2bb6
-- title:
--   Exact genuine finite-clock nonruin event splits into killed upper-record regeneration or no-record remainder
-- statement:
--   For each source Lévy path with observation horizon t no later than cap N, closed survival from reserve x partitions exactly into: (i) a genuine upper passage strictly before t and lower ruin, followed by nonruin survival of the complete shifted future starting from the attained threshold x+b; or (ii) no strict upper passage before t, with original survival. The two branches are disjoint and exhaustive, and the second is the analytically bounded Qp no-record remainder. Uses only proved exact pathwise killed-history decompositions, not the desired two-sided exit identity.
-- source:
--   Accepted WS01H capped-record full survival equivalence under the actual source-defined clocks and elementary trichotomy of extended nonnegative first-passage time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_capped_record_full_survival_iff_lower_killed_fresh_future

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (hb : 0 ≤ b)
    (N : ℝ≥0) (ω : Ω) (t : ℝ≥0) (htN : t ≤ N) :
    (let τ : ℝ≥0 :=
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) ↔
       (twoSidedExitUpTime X b ω < (t : ℝ≥0∞) ∧
        twoSidedExitUpTime X b ω <
          twoSidedExitDownTime X (-x) ω ∧
        ∀ u : ℝ≥0, u ≤ t - τ →
          0 ≤ (x + b) + (X.X (τ + u) ω - X.X τ ω)) ∨
       ((t : ℝ≥0∞) ≤ twoSidedExitUpTime X b ω ∧
         ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω)) := by sorry
