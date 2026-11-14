-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_truly_jumpless_large_mark_sum_identically_zero
-- name    : AvramDividend.Classical.avram_a22_original_truly_jumpless_large_mark_sum_identically_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:50:33.945831+00:00
-- url     : https://prove2.me/theorems/0e5a9e09-15ae-488b-a7cf-f41b7acd0780
-- title:
--   Physical uncompensated large negative jump sum vanishes on an original no-jump path
-- statement:
--   On a single actual original sample path whose every strictly positive time has zero jump, the pathwise uncompensated large negative jump sum is exactly zero at all horizons, irrespective of the Levy triplet. The proof empties the physical jump-time counting-measure support. No Gaussian companion process is introduced.
-- source:
--   Original physical large-jump source definition in Avram mission. Kyprianou Levy-Ito finite-activity decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_truly_jumpless_large_mark_sum_identically_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNoJump : ∀ u : ℝ≥0, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0)
    (t : ℝ≥0) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = 0 := by sorry
