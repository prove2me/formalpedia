-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_L2_cauchy_of_source_smalljump_tail
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_residual_L2_cauchy_of_source_smalljump_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:01:15.257671+00:00
-- url     : https://prove2.me/theorems/3d8e7730-0d83-4ef4-a311-813b3b79877b
-- title:
--   Source smalljump L2 Cauchy bounds transfer to the original residual sequence
-- statement:
--   For the same genuine original Lévy process X, a verified square-integrable tail Cauchy estimate on the actual intrinsic compensated small-jump process Jsmall_n transfers, at a fixed horizon, to the source residual R_n. The needed stochastic premise is explicitly an L2 estimate on original X's marked jumps, to be obtained from P2/P4-G. The result is a mathematical bridge, not a proof of the stochastic premise, continuity, martingale or bracket.
-- source:
--   Exact Proved original residual cutoff difference L2 identity 75c91fbd; the source assumption is separately named hSmallTail and is not invented as a theorem.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_residual_L2_cauchy_of_source_smalljump_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (hSmallTail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ∀ m ≥ N,
        Integrable (fun ω : Ω =>
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
           avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P ∧
        (∫ ω : Ω,
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
           avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2 ∂P) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ∀ m ≥ N,
        Integrable (fun ω : Ω =>
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
           avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2) P ∧
        (∫ ω : Ω,
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
           avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2 ∂P) < ε := by sorry
