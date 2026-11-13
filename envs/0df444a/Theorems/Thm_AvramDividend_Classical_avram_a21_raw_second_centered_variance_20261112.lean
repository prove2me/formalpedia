-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_raw_second_centered_variance_20261112
-- name    : AvramDividend.Classical.avram_a21_raw_second_centered_variance_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:20:17.831916+00:00
-- url     : https://prove2.me/theorems/aaeb5fe2-0651-4268-94dc-15c93c7ac2a4
-- title:
--   Real centred second moment from exact raw first and second moments
-- statement:
--   On a probability space, for an integrable real random variable with integrable square and exact first and second raw moments, derive the exact second moment after subtracting the mean. This is the algebraic bridge for compensated source Borel jump integrals.
-- source:
--   Proved physically specialised variance argument 4aad78f4-17d0-41e4-8264-0415381fbf46, with the source-specific count hypotheses removed. Mathlib integral_add, integral_sub, integral_const_mul.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a21_raw_second_centered_variance_20261112
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (J : Ω → ℝ) (r q : ℝ)
    (hJ : Integrable J P)
    (hJ2 : Integrable (fun ω => (J ω) ^ 2) P)
    (hFirst : (∫ ω, J ω ∂P) = r)
    (hSecond : (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + q) :
    (∫ ω, (J ω - r) ^ 2 ∂P) = q := by sorry
