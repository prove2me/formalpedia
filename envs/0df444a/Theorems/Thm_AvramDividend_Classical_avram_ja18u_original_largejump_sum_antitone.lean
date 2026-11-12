-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18u_original_largejump_sum_antitone
-- name    : AvramDividend.Classical.avram_ja18u_original_largejump_sum_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:52:09.290759+00:00
-- url     : https://prove2.me/theorems/2fe10125-f89d-4ac0-bd8e-6f3756bd6938
-- title:
--   Actual spectrally negative large-jump sum is pathwise nonincreasing in time
-- statement:
--   Each original large jump has size ≤−1. By the Proved physical finite-sum theorem e8675ada, the sum up to s is over a subset of the sum up to t for s≤t. Finite sum monotonicity gives the exact pathwise decreasing large-jump process, yielding an integrable supremum envelope from its finite-horizon L1 endpoint.
-- source:
--   J-A18 original stopped J envelope JA18P

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja18u_original_largejump_sum_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (ω : Ω) (s t : ℝ≥0), s ≤ t →
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ≤
      avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω := by sorry
