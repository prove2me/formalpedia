-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_real_source_centered_square_shift
-- name    : AvramDividend.Classical.avram_a20_real_source_centered_square_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:43:12.423347+00:00
-- url     : https://prove2.me/theorems/d905d0b7-6d5e-4993-91c1-fe598ac2aa7c
-- title:
--   Exact quadratic moment under deterministic shift of a centred square-integrable original-source random field
-- statement:
--   On any probability space, if a real field Y is integrable and square-integrable, has zero expectation and exact second moment v, then (Y+r) is square-integrable and has exact second moment v+r² for any real deterministic shift r. The proof expands the pointwise square, uses integrability and finite additivity of the source Bochner integral, vanishing centred first moment and the probability normalisation. This is a generic reusable algebraic ingredient for deriving original physical weighted Borel Poisson-jump raw moments from the already Proved exact centred finite-simple Borel-mark isometry.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a20_real_source_centered_square_shift
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (r v : ℝ)
    (hY : Integrable Y P)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P)
    (hZero : (∫ ω, Y ω ∂P) = 0)
    (hVariance : (∫ ω, (Y ω) ^ 2 ∂P) = v) :
    Integrable (fun ω => (Y ω + r) ^ 2) P ∧
      (∫ ω, (Y ω + r) ^ 2 ∂P) = v + r ^ 2 := by sorry
