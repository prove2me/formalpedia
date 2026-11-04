-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_levy_measure_nonnegative_mark_simple_lintegral
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_levy_measure_nonnegative_mark_simple_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:23:26.022138+00:00
-- url     : https://prove2.me/theorems/704f9964-e3a5-496b-971f-76bb9022b36a
-- title:
--   Original Levy measure integral of a nonnegative finite mark-simple kernel
-- statement:
--   The integral of a nonnegative finite mark-simple function against the given original spectrally negative Levy measure X.nu equals the weighted finite sum of its mark-band masses.
-- source:
--   Pinned Mathlib finite-sum lintegral and indicator integral, original process Levy measure X.nu.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_levy_measure_nonnegative_mark_simple_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) :
    (∫⁻ z : ℝ, ∑ i ∈ S, (B i).indicator (fun _ => c i) z ∂X.ν) =
      ∑ i ∈ S, c i * X.ν (B i) := by sorry
