-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_weighted_mark_cutoff_lintegral_iSup
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_weighted_mark_cutoff_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:04:59.751622+00:00
-- url     : https://prove2.me/theorems/e15b0a44-6ab8-450a-9880-1a38147202b9
-- title:
--   Original weighted intrinsic jump integral monotone cutoff limit
-- statement:
--   For original intrinsic jumps, a constant nonnegative marked weight integrates continuously from below over increasing measurable mark cutoffs at each original path.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_weighted_mark_cutoff_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : ℕ → Set ℝ) (hMon : Monotone B)
    (hB : ∀ n, MeasurableSet (B n)) (c : ℝ≥0∞) (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ,
      (Ioc s t ×ˢ (⋃ n, B n)).indicator (fun _ => c) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ⨆ n, (∫⁻ p : ℝ≥0 × ℝ,
      (Ioc s t ×ˢ B n).indicator (fun _ => c) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
