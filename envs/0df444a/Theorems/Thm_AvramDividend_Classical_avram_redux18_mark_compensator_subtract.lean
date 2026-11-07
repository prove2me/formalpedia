-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_mark_compensator_subtract
-- name    : AvramDividend.Classical.avram_redux18_mark_compensator_subtract
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:06:37.449317+00:00
-- url     : https://prove2.me/theorems/a6c21247-9bb2-4f46-bbcf-0465897e0da4
-- title:
--   Finite mark-band exponential compensator subtraction identity
-- statement:
--   For any measurable mark band on which constant one and the exponential mark weight are integrable, the Lévy-style exponential compensator integral of 1 minus exp(y) equals the band's real total measure minus its exponential mark moment. This exactly connects compound-Poisson mark moments with the compensator in the original finite-cutoff Lévy jump Laplace functional.
-- source:
--   Deterministic finite-mark compensator identity; paired with the accepted Poisson-count and finite-partition transforms, the original-path argument still requires source-exact independent-band counts and approximation.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exponential
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_redux18_mark_compensator_subtract
    (ν : Measure ℝ) (B : Set ℝ)
    (hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) B ν)
    (hExp : IntegrableOn Real.exp B ν) :
    (∫ y in B, (1 - Real.exp y) ∂ν) =
      (ν B).toReal - (∫ y in B, Real.exp y ∂ν) := by sorry
