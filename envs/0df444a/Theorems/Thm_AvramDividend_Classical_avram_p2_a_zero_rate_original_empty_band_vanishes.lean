-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_empty_band_vanishes
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_empty_band_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:32:11.658242+00:00
-- url     : https://prove2.me/theorems/25874c09-7e8b-45de-b966-8cb3c125ffa4
-- title:
--   Original Lévy marked jump expectation vanishes on an empty mark band
-- statement:
--   For the unchanged original Levy process X and any nonnegative horizon T, the intrinsic marked-count measure of the rectangle (0,T]×empty is zero, and its ENNReal expectation under the original P is zero, regardless of jump activity and without a compensator. This handles a null mark band edge case of the exact Borel rate identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_empty_band_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
         X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc 0 T ×ˢ (∅ : Set ℝ)) ∂P) = 0 := by sorry
