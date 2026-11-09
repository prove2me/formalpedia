-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_smalljump_tsum_eventually_zero_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_smalljump_tsum_eventually_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T21:42:57.530192+00:00
-- url     : https://prove2.me/theorems/fa3263d5-a466-40b9-a6e7-06bccd0d66d3
-- title:
--   Original finite-activity small-jump series eventually vanishes on bounded horizons
-- statement:
--   On the same original Levy probability space under finite negative-jump activity, for almost every path and each bounded clock, there is one reciprocal small-jump cutoff beyond which the signed physical jump-time tsum is exactly zero. This removes the random small-jump source in the intrinsic stopped Ito-Meyer decomposition without replacing the source process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_smalljump_tsum_eventually_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ T ∧
            |X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u| ≤
              1 / ((k : ℝ) + 1) then
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        else 0) = 0 := by sorry
