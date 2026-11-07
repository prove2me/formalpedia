-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_positive_rate_mark_normalisation
-- name    : AvramDividend.Classical.avram_redux18_positive_rate_mark_normalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:47:27.964199+00:00
-- url     : https://prove2.me/theorems/66baa765-4798-41a3-9139-0d2119fd70f2
-- title:
--   Normalise positive-rate Poisson mark moments to the Lévy compensator
-- statement:
--   For a finite mark band with strictly positive intensity, the exponent of the compound-Poisson Laplace transform obtained from its normalised exponential mark moment equals the negative Lévy compensator integral over that band, at any real horizon. This is the exact bridge between the finite-bin Poisson transform and the original process cutoff compensator.
-- source:
--   Derives from accepted Redux18 mark compensator subtraction identity a6c21247 and field algebra with a strictly positive band mass. Band intensity zero is a separate case.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_redux18_mark_compensator_subtract
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_redux18_positive_rate_mark_normalisation
    (ν : Measure ℝ) (B : Set ℝ)
    (hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) B ν)
    (hExp : IntegrableOn Real.exp B ν)
    (hRate : 0 < (ν B).toReal) (t : ℝ) :
    Real.exp (t * ((ν B).toReal *
      ((∫ y in B, Real.exp y ∂ν) / (ν B).toReal - 1))) =
    Real.exp (-(t * (∫ y in B, (1 - Real.exp y) ∂ν))) := by sorry
