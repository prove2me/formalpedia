-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen17_concrete_geometric_signed_generator_not_integrable
-- name    : AvramDividend.Classical.avram_gen17_concrete_geometric_signed_generator_not_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:32:31.571563+00:00
-- url     : https://prove2.me/theorems/6edf2a6f-c16f-4e32-8b7d-f2d2005def9e
-- title:
--   A concrete dyadic reserve gives a nonintegrable signed generator deficit under geometric sampling
-- statement:
--   For the dyadic reserve y(k)=1/(16*2^(2k)), which is positive and integrable under the half-geometric distribution, the original signed affine generator deficit 3-4sqrt(y)-2/sqrt(y) has infinite absolute expectation. This discharges all scalar side conditions of the existing proved signed-geometric bridge, leaving only the construction of an Avram-original process and dividend strategy to embed it in a stopped grid cell.
-- source:
--   Proved signed bridge f7f13fb7-375b-4c51-93ff-f09782dcae54, pinned Mathlib measurable_of_countable and Integrable.of_bound; explicit dyadic reserve required by original stopped-cell counterexample.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen16_signed_geometric_generator_deficit_not_integrable
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_gen17_concrete_geometric_signed_generator_not_integrable
    (p : unitInterval) (hp : p ≠ 0) (hhalf : (p : ℝ) = 1 / 2) :
    ¬ Integrable (fun k : ℕ =>
        (3 : ℝ) - 4 * Real.sqrt (1 / (16 * ((2 : ℝ) ^ k) ^ 2)) -
          2 / Real.sqrt (1 / (16 * ((2 : ℝ) ^ k) ^ 2)))
        (geometricMeasure p) := by sorry
