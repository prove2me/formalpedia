-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_levy_measure_monotone_cutoff_annulus_increment
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_levy_measure_monotone_cutoff_annulus_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:48:55.653197+00:00
-- url     : https://prove2.me/theorems/69e2608b-ce9c-4364-935f-f6ec4726f4cd
-- title:
--   Original Levy intensity cutoff increment is the disjoint mark annulus intensity
-- statement:
--   For a monotone sequence of measurable mark sets, the actual original Levy measure mass at the next cutoff is the sum of the previous cutoff mass and mass in the disjoint intervening mark annulus.
-- source:
--   Original spectrally negative Levy source intensity X.nu, measure_union and Borel mark partition identities at pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_levy_measure_monotone_cutoff_annulus_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℕ → Set ℝ) (hMon : Monotone B)
    (hB : ∀ n, MeasurableSet (B n)) (n : ℕ) :
    X.ν (B (n + 1)) =
      X.ν (B n) + X.ν (B (n + 1) \ B n) := by sorry
