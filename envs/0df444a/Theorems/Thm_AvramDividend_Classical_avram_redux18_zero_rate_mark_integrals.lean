-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_zero_rate_mark_integrals
-- name    : AvramDividend.Classical.avram_redux18_zero_rate_mark_integrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:15:38.536298+00:00
-- url     : https://prove2.me/theorems/2640052f-23b8-4b44-985c-c049f2892301
-- title:
--   Zero-intensity jump-band mark moment and compensator vanish
-- statement:
--   If a jump-mark band has zero Lévy measure then its exponential mark moment and its finite-cutoff Laplace compensator integral both vanish, with no integrability hypothesis. This is the zero-rate branch complementary to the positive-rate normalisation.
-- source:
--   Exact consequence of Measure.restrict_eq_zero at the pinned Mathlib revision, followed by zero-measure Bochner integrals. Complements Redux18 positive-rate normalisation for mark partitions containing measure-zero bands.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.SpecialFunctions.Exponential
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_redux18_zero_rate_mark_integrals
    (ν : Measure ℝ) (B : Set ℝ) (hZero : ν B = 0) :
    (∫ y in B, Real.exp y ∂ν) = 0 ∧
      (∫ y in B, (1 - Real.exp y) ∂ν) = 0 := by sorry
