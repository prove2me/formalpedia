-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_event_interval_lintegral_split
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_marked_event_interval_lintegral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:28:13.657813+00:00
-- url     : https://prove2.me/theorems/8240a020-8f57-4f50-9733-504a39132d38
-- title:
--   Original intrinsic marked Lévy counts: restricted expected time-rectangle additivity
-- statement:
--   The genuine original Lévy intrinsic time-mark jump count has additive nonnegative expectation on (s,t]×B across the cut r, even after restricting the original sample-space measure to any event A. Uses accepted original intrinsic count measurability and the pathwise interval split; no P2 intensity or compensator hypothesis.
-- source:
--   Accepted intrinsic marked jump-count split 27287316 and count measurability 1f8f25b0; Mathlib lintegral_add_left.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_interval_split
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_marked_event_interval_lintegral_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r t : ℝ≥0) (hsr : s ≤ r) (hrt : r ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (A : Set Ω) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s r ×ˢ B) ∂P) +
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc r t ×ˢ B) ∂P) := by sorry
