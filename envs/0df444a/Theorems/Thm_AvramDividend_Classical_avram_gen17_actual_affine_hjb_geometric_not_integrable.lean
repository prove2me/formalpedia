-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen17_actual_affine_hjb_geometric_not_integrable
-- name    : AvramDividend.Classical.avram_gen17_actual_affine_hjb_geometric_not_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:52:39.48314+00:00
-- url     : https://prove2.me/theorems/687f069c-4a07-44d5-b043-842cdbbb9596
-- title:
--   The actual affine HJB generator deficit is nonintegrable on a dyadic geometric reserve
-- statement:
--   The exact affine generator deficit 3 + y - 4sqrt(y) - 2/sqrt(y), arising in the Proved Avram global HJB sign lemma 90f12395, is not absolutely integrable when dyadic positive reserves y=1/(16*2^(2k)) are sampled under a half-geometric law. The extra plus-y contribution is itself integrable and cannot repair the nonintegrable signed singularity proved in 6edf2a6f. This is a scalar stochastic-integrability obstruction and does not itself establish an original-process counterexample.
-- source:
--   Affine singular original HJB sign theorem 90f12395-8e76-4861-a0a6-710521285d52; accepted scalar nonintegrability 6edf2a6f-c16f-4e32-8b7d-f2d2005def9e; finite-measure bounded integrability.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen17_concrete_geometric_signed_generator_not_integrable
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_gen17_actual_affine_hjb_geometric_not_integrable (p : unitInterval) (hp : p ≠ 0) (hhalf : (p : ℝ) = 1 / 2) : ¬ Integrable (fun k : ℕ => (3 : ℝ) + 1 / (16 * ((2 : ℝ) ^ k) ^ 2) - 4 * Real.sqrt (1 / (16 * ((2 : ℝ) ^ k) ^ 2)) - 2 / Real.sqrt (1 / (16 * ((2 : ℝ) ^ k) ^ 2))) (geometricMeasure p) := by sorry
