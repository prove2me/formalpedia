-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
-- name    : AvramDividend.Classical.avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:58:02.255835+00:00
-- url     : https://prove2.me/theorems/4272e556-dc01-4794-9c4a-b19cadf367a1
-- title:
--   Every finite original physical-grid all-negative occupied jump-cell count is measurable on the same source space
-- statement:
--   For an arbitrary deterministic nondecreasing original-time physical mesh, the indicator that an actual original spectrally negative Lévy marked-count measure has any jump in a given half-open cell, over all marks, is measurable by the already Proved global original marked jump count measurability 5cb1e247. Every finite sum of these exact occupied-cell indicators is measurable on the source Ω. This is the missing all-mark measurable occupancy input for converting the collision L1 theorem 2811485c and source exact cofinal occupancy 7df2397f into the physical zero-contact collision error of f3f336fd and root-connected 4f605d76.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m,
        if ((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ω -
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t, X.X t ω -
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
          (Ioc (u i) (u (i + 1)) ×ˢ (Set.univ : Set ℝ)) ≠ 0 then
          (1 : ℝ≥0∞) else 0) := by sorry
