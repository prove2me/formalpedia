-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_real_window_count_additive
-- name    : AvramDividend.Classical.avram_mix_annulus15_original_real_window_count_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:45:17.68873+00:00
-- url     : https://prove2.me/theorems/836786f5-9fce-4e31-b654-23edfeb38729
-- title:
--   Original physical chronological annulus real count equals nested negative-cutoff count difference
-- statement:
--   For any original physical time window (s,t] and nested negative mark cutoffs n≤m, the real-valued actual marked count at the larger cutoff is exactly the smaller-cutoff real count plus the real annulus count. Finiteness follows from original finite marked jump-time cardinal theorems. This provides a correct same-space source identity for subtracting two Proved full-cutoff predictable L2 compensated martingales to build the annulus predictable martingale needed in the infinite-activity route.
-- source:
--   Root-connected physical same-path marked count identity. Proved source mark-union additivity, Proved full-cutoff and annulus finite card bridge; downstream random bounded predictable annulus finite-grid L2 and mean-zero via Proved 06c6a15a, then 5f12c023 and f5e6e083.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus14_original_window_filter_card
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus15_original_real_window_count_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (hst : s ≤ t) (n m : ℕ) (hnm : n ≤ m) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    let J : Set ℝ → ℝ≥0∞ := fun B =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    (J (Iic d)).toReal =
      (J (Iic c)).toReal + (J (Ioc c d)).toReal := by sorry
