-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_count_nonfinite
-- name    : AvramDividend.Classical.avram_a19_singular_count_nonfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:47:29.413211+00:00
-- url     : https://prove2.me/theorems/fc8619a9-5117-4398-a6ac-7d90c44b0cdd
-- title:
--   Dyadic singular generator loss has infinite counting-measure absolute integral
-- statement:
--   The weighted near-zero generator-loss function of an arbitrary dyadic surplus sequence is not of finite absolute integral against counting measure on natural numbers. It follows from the proved non-summability result via the Mathlib equivalence between finite counting integrals and summability of norms.
-- source:
--   A19 source-exact generator-cell disproof research, 7 November 2026; scalar HasFiniteIntegral reduction.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_weighted_series_not_summable
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_count_nonfinite
    (y : Nat -> Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (MeasureTheory.HasFiniteIntegral (fun k : Nat =>
      (-(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))) /
        (2 : Real) ^ k) MeasureTheory.Measure.count) := by sorry
