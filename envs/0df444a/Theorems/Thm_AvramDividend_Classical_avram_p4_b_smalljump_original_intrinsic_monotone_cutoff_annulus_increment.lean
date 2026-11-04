-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_monotone_cutoff_annulus_increment
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_monotone_cutoff_annulus_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:18:55.094749+00:00
-- url     : https://prove2.me/theorems/39c5ba99-e917-4446-9f20-0e76fd00f66c
-- title:
--   Original intrinsic jump count cutoff increments equal disjoint annulus count
-- statement:
--   For an increasing sequence of Borel mark bands, the change in the actual original Levy marked jump count between consecutive cutoffs is the count on the disjoint intervening mark annulus.
-- source:
--   Original intrinsic marked jump measure and previously Proved disjoint mark union count identity on the same source path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_monotone_cutoff_annulus_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : ℕ → Set ℝ)
    (hMon : Monotone B) (hB : ∀ n, MeasurableSet (B n))
    (n : ℕ) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B (n + 1)) =
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B n) +
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (B (n + 1) \ B n)) := by sorry
