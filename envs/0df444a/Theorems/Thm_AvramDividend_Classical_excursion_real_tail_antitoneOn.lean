-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_real_tail_antitoneOn
-- name    : AvramDividend.Classical.excursion_real_tail_antitoneOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:09:10.445853+00:00
-- url     : https://prove2.me/theorems/ddfc4aa9-6efe-4a00-a370-c66f39c7874f
-- title:
--   The finite real upper-tail mass of a positive excursion measure is antitone
-- statement:
--   For any positive Borel measure with finite upper-tail mass above each x>0, the real-valued function x↦μ([x,∞)) is antitone on (0,∞). This gives the exact order property of the descending-excursion height tail appearing in W′(x)=W(x)(φ+μ([x,∞))), and is a prerequisite for logarithmic derivative monotonicity.
-- source:
--   Mathlib measure_mono, Ici_subset_Ici and ENNReal.toReal_mono; excursion derivative representation.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.excursion_real_tail_antitoneOn
    (μ : Measure ℝ)
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    AntitoneOn (fun x : ℝ => μ.real (Ici x)) (Ioi (0 : ℝ)) := by sorry
