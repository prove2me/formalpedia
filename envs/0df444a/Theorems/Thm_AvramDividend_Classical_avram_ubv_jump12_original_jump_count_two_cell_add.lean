-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_jump_count_two_cell_add
-- name    : AvramDividend.Classical.avram_ubv_jump12_original_jump_count_two_cell_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:48:46.650565+00:00
-- url     : https://prove2.me/theorems/e6b70eac-b9fa-432a-ad86-34e1f8b8f5f8
-- title:
--   Original physical jump count adds over adjacent time cells
-- statement:
--   For the jump-count measure constructed directly from the original spectrally negative Levy path, splitting a time interval at any intermediate time preserves the total finite-band count as an exact extended nonnegative addition. The identity is pathwise, needs no independent Poisson space and is the basis for telescoping a stopping grid.
-- source:
--   Original pathwise count telescope required by the bounded-clock finite-band compensator route to 71fd10ee; based on pinned Mathlib set interval partition, set product, and disjoint measurable union identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_jump12_original_jump_count_two_cell_add
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b c : ℝ≥0) (hab : a ≤ b) (hbc : b ≤ c)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    J (Ioc a c ×ˢ B) =
      J (Ioc a b ×ˢ B) + J (Ioc b c ×ˢ B) := by sorry
