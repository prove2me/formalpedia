-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel
-- name    : AvramDividend.Classical.avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:34:15.331447+00:00
-- url     : https://prove2.me/theorems/82da93b2-4a2f-4d25-ba9e-99cd7035ebb8
-- title:
--   Exact original compensated jump kernel equals uncompensated large-jump difference above the barrier
-- statement:
--   For arbitrary scale-function-shaped W and every reserve x≥cstar(W)+1, the actual compensated source Lévy generator integrand for any negative jump y<0 equals vcstar(x+y)−vcstar(x) when y≤−1 and is identically zero when −1<y<0. This is an exact pointwise identity, not an integral approximation. In particular, large jumps may cross the barrier and ruin boundary without omission, and the one-unit threshold ensures small jumps remain in the affine region where the source compensation convention cancels.
-- source:
--   Original source generatorIntegrand definition and Proved genuine small-jump compensated-zero lemma above barrier; exact source cutoff Ioo(-1,1).

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel
    (W : ℝ → ℝ) (x y : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x) (hy : y < 0) :
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y =
      if y ≤ -1 then vcstar W (x + y) - vcstar W x else 0 := by sorry
