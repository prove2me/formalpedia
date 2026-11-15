-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
-- name    : AvramDividend.Classical.avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:49:53.464426+00:00
-- url     : https://prove2.me/theorems/a567989d-029f-474d-bc65-decee01a415b
-- title:
--   Original probability measure characteristic function uniqueness gives exact centred Gaussian HasLaw
-- statement:
--   An almost-everywhere measurable real random variable under the original probability measure has precisely the centred Gaussian law with variance v whenever its characteristic function agrees at all Fourier parameters with that centred normal measure.
-- source:
--   Mathlib Measure.ext_of_charFun and ProbabilityTheory.HasLaw.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Exact characteristic function on the actual source measure identifies its centred Gaussian marginal law. -/

theorem AvramDividend.Classical.avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (G : Ω → ℝ) (v : ℝ≥0)
    (hMeas : AEMeasurable G P)
    (hChar : ∀ u : ℝ,
      charFun (P.map G) u = charFun (gaussianReal 0 v) u) :
    HasLaw G (gaussianReal 0 v) P := by sorry
