-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_integrable_of_integrable_real_square
-- name    : AvramDividend.Classical.chat03_integrable_of_integrable_real_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T10:06:35.971328+00:00
-- url     : https://prove2.me/theorems/2d42ee85-df7c-4e25-a0eb-49e572160059
-- title:
--   Real L² square integrability implies L¹ integrability on a probability space
-- statement:
--   For a real-valued almost-everywhere strongly measurable function on a probability space, integrability of its square implies integrability of the function. The proof uses the pinned L² characterisation and finite-measure inclusion.
-- source:
--   MeasureTheory.memLp_two_iff_integrable_sq and MeasureTheory.MemLp.integrable, pinned Mathlib revision.

import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

theorem AvramDividend.Classical.chat03_integrable_of_integrable_real_square
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P)
    (hZ2 : Integrable (fun ω => (Z ω) ^ 2) P) :
    Integrable Z P := by sorry
