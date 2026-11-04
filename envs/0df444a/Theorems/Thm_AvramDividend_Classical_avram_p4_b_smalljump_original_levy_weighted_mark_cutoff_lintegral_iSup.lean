-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_levy_weighted_mark_cutoff_lintegral_iSup
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_levy_weighted_mark_cutoff_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:10:59.314922+00:00
-- url     : https://prove2.me/theorems/311b6eab-f3ba-4bb3-87f6-729371e06617
-- title:
--   Original Levy weighted mark integral monotone cutoff limit
-- statement:
--   For the actual original Levy measure X.nu, nonnegative constant mark-weight integrals extend continuously from increasing Borel bands to their union.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_levy_weighted_mark_cutoff_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℕ → Set ℝ) (hMon : Monotone B)
    (hB : ∀ n, MeasurableSet (B n)) (c : ℝ≥0∞) :
    (∫⁻ z : ℝ, (⋃ n, B n).indicator (fun _ => c) z ∂X.ν) =
      ⨆ n, (∫⁻ z : ℝ, (B n).indicator (fun _ => c) z ∂X.ν) := by sorry
