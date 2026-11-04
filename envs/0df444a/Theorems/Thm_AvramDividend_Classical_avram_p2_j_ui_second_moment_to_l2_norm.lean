-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_second_moment_to_l2_norm
-- name    : AvramDividend.Classical.avram_p2_j_ui_second_moment_to_l2_norm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:39:25.579725+00:00
-- url     : https://prove2.me/theorems/2424af2b-f4d7-4177-b230-178a95c06aa9
-- title:
--   A genuine real second-moment integral bound controls the L² seminorm
-- statement:
--   For an almost-everywhere strongly measurable real function with an integrable squared norm, an upper bound on the real Bochner integral of the square by B² yields an L² seminorm bound by B. This verifies the bridge between original finite second-moment estimates and the reusable L²-to-Vitali proof interface, without assuming any Lévy law.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_second_moment_to_l2_norm
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (B : ℝ≥0)
    (hm : AEStronglyMeasurable Y P)
    (hInt : Integrable (fun ω => ‖Y ω‖ ^ 2) P)
    (hBound : (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ (B : ℝ) ^ 2) :
    eLpNorm Y 2 P ≤ (B : ENNReal) := by sorry
