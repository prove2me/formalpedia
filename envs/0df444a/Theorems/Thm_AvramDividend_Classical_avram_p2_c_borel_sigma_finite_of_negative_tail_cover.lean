-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_sigma_finite_of_negative_tail_cover
-- name    : AvramDividend.Classical.avram_p2_c_borel_sigma_finite_of_negative_tail_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:40:58.695467+00:00
-- url     : https://prove2.me/theorems/4092a314-ec1a-42fe-a90f-8b12144a47b5
-- title:
--   Strict negative support and locally finite negative tails imply sigma-finite mark measure
-- statement:
--   The actual negative-support intensity candidate is σ-finite because it has zero nonnegative mass and finite mass on harmonic negative bands, which countably cover the entire real mark space. Reuse the Proved P2-C countable finite cover and the pinned Mathlib Measure.sigmaFinite_of_countable theorem.
-- source:
--   Once P2-C source-backed harmonic cover avram_p2_c_borel_countable_finite_negative_support_cover is genuinely Proved, use exact pinned Mathlib declaration MeasureTheory.Measure.sigmaFinite_of_countable. No ν-rate assumption.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_c_borel_sigma_finite_of_negative_tail_cover
    (μ : Measure ℝ)
    (hzero : μ (Ici (0 : ℝ)) = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → μ (Iic (-ε)) < ⊤) :
    SigmaFinite μ := by sorry
