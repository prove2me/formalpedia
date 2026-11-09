-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_nested_cutoff_annulus_count_additive
-- name    : AvramDividend.Classical.avram_mixed_source13_original_nested_cutoff_annulus_count_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:16:54.326191+00:00
-- url     : https://prove2.me/theorems/f0104cbc-54eb-41b5-89a3-49ac9d59377e
-- title:
--   Original physical nested cutoff count splits at the annulus
-- statement:
--   For the unchanged spectrally negative Levy path and the true marked jump count on (0,T], the cutoff count at m equals the cutoff count at n plus the disjoint negative annulus count, for n≤m. This exact same-path count identity is needed for constructing annulus predictable past counts and mixed source covariance, and assumes no independent thinning or auxiliary process.
-- source:
--   MIX-SOURCE13 original annulus factorisation used to derive physical annulus source moments and L2 grid isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_original_nested_cutoff_annulus_count_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) (ω : Ω) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    let J : Set ℝ → ℝ≥0∞ := fun B =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    J (Iic d) = J (Iic c) + J (Ioc c d) := by sorry
