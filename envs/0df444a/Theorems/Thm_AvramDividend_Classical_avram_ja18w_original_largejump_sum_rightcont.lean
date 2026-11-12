-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18w_original_largejump_sum_rightcont
-- name    : AvramDividend.Classical.avram_ja18w_original_largejump_sum_rightcont
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:00:24.783395+00:00
-- url     : https://prove2.me/theorems/b2377e1f-53c5-43b4-9b09-baf32fb19a75
-- title:
--   Original actual large-negative-jump cumulative sum is right-continuous on every sample path
-- statement:
--   For any original càdlàg X path, the times carrying jumps ≤−1 form a finite set on each compact interval. Proved e8675ada represents the large-jump integral as the sum over that literal set. A finite cumulative jump sum is right-continuous, including at jump times because the summation interval is closed on the right. This remaining physical regularity is needed to apply proved optional sampling to J.
-- source:
--   J-A18 finite-activity original J right continuity JA18P

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18w_original_largejump_sum_rightcont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt
        (fun u : ℝ≥0 =>
          avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω)
        (Set.Ici t) t := by sorry
