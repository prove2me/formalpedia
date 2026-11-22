-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_generic_centered_cross_zero_from_three_square_moments_20261122
-- name    : AvramDividend.Classical.avram_oai_generic_centered_cross_zero_from_three_square_moments_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:26:28.521118+00:00
-- url     : https://prove2.me/theorems/af4bd140-c2b7-420a-b21c-7bd7bd8e11cc
-- title:
--   Centred count orthogonality and cross integrability from exact variances of two cells and their union
-- statement:
--   For square-integrable real random variables Y,Z with known second moments E[Y²]=a, E[Z²]=b and E[(Y+Z)²]=a+b, their product YZ is integrable and E[YZ]=0. The proof is the exact polarisation identity YZ=((Y+Z)²−Y²−Z²)/2. This lemma will transfer the newly proved original all-activity negative Borel count variance for three disjoint source mark sets into exact cross-mark zero covariance, removing global finite jump intensity from finite-simple-mark isometry.

import Mathlib
open MeasureTheory
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_generic_centered_cross_zero_from_three_square_moments_20261122
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Y Z : Ω → ℝ) (a b : ℝ)
    (hY : Integrable (fun ω => (Y ω) ^ 2) P)
    (hZ : Integrable (fun ω => (Z ω) ^ 2) P)
    (hSum : Integrable (fun ω => (Y ω + Z ω) ^ 2) P)
    (hEY : (∫ ω, (Y ω) ^ 2 ∂P) = a)
    (hEZ : (∫ ω, (Z ω) ^ 2 ∂P) = b)
    (hESum : (∫ ω, (Y ω + Z ω) ^ 2 ∂P) = a + b) :
    Integrable (fun ω => Y ω * Z ω) P ∧
    (∫ ω, Y ω * Z ω ∂P) = 0 := by sorry
