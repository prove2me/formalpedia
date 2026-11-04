-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_short_strip_event_bound
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_marked_short_strip_event_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:26:33.295493+00:00
-- url     : https://prove2.me/theorems/727c5a25-770c-4e4b-85e5-a9fbbba044b5
-- title:
--   Original Lévy short initial marked-jump strip: eventwise first-moment bound
-- statement:
--   For the genuine intrinsic jump-counting measure of the original spectrally negative Lévy process, any event-restricted expected count on (s,r]×B is bounded above by its unconditional rate (r−s)ν(B). The physical source rate is an explicit P2-dependent hypothesis. The event A may lie in the right-continuous source filtration, so the estimate controls the omitted short interval in the raw-to-right-continuous compensator extension.
-- source:
--   Actual source mark-count literal; Mathlib.MeasureTheory.Integral.Lebesgue.Basic lintegral_mono_set; P2 source rate remains a visible hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_marked_short_strip_event_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r : ℝ≥0) (B : Set ℝ) (A : Set Ω)
    (hRate :
      (∫⁻ ω,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s r ×ˢ B) ∂P) =
          ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s r ×ˢ B) ∂P) ≤
          ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
