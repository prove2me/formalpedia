-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_not_integrable
-- name    : AvramDividend.Classical.avram_a19_singular_geometric_not_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:29:07.140048+00:00
-- url     : https://prove2.me/theorems/3adb6269-cda1-44bc-bc14-4e92e6319e16
-- title:
--   Singular generator loss is nonintegrable under a geometric probability law
-- statement:
--   For a success-probability-one-half geometric measure on natural numbers and positive surplus y_k at most 1/16 and 2^(-2k), the explicit source generator loss profile has infinite absolute expectation. This is a genuine probability-measure obstruction and a direct intermediate component of the proposed A19 counterexample, relying on Mathlib geometricMeasure and integrable_geometricMeasure_iff.
-- source:
--   A19 original generator-cell counterexample research, 7 November 2026; source-exact prior singular power bound f4d7a827; Mathlib Probability.Distributions.Geometric.

import Mathlib.Probability.Distributions.Geometric
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_power_cell_bound
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_geometric_not_integrable
    (p : unitInterval) (hp : p != 0) (hhalf : (p : Real) = 1 / 2)
    (y : Nat -> Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (MeasureTheory.Integrable (fun k : Nat =>
      -(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k)))
      (ProbabilityTheory.geometricMeasure p)) := by sorry
