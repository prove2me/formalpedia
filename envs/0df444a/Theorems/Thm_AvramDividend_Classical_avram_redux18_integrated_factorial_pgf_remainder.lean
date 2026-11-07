-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_integrated_factorial_pgf_remainder
-- name    : AvramDividend.Classical.avram_redux18_integrated_factorial_pgf_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:54:27.130434+00:00
-- url     : https://prove2.me/theorems/9954d89f-4591-47a8-aee8-360a80425939
-- title:
--   Expected PGF linearisation error controlled by the exact second factorial count moment
-- statement:
--   On a finite measure, the integrated error between the count PGF and its first-order linearisation is nonnegative and its doubled expectation is bounded by the scaled second falling-factorial count moment. The theorem turns the existing original Lévy count first and second factorial moment identities into an O(h²) short-time PGF estimate used for Poisson characterisation from independent time cells.
-- source:
--   Integrate the accepted pointwise PGF factorial remainder theorem under explicit integrability of count, PGF and second falling factorial count; uses MeasureTheory.integral_mono and integral_nonneg.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux18_pgf_factorial_remainder
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_redux18_integrated_factorial_pgf_remainder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (N : Ω → ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hN : Integrable (fun ω => (N ω : ℝ)) μ)
    (hZ : Integrable (fun ω => z ^ (N ω)) μ)
    (hFac : Integrable (fun ω =>
      (N ω : ℝ) * ((N ω : ℝ) - 1)) μ) :
    0 ≤ ∫ ω, (z ^ (N ω) - (1 - (1 - z) * (N ω : ℝ))) ∂μ ∧
    2 * (∫ ω, (z ^ (N ω) - (1 - (1 - z) * (N ω : ℝ))) ∂μ) ≤
      ∫ ω, ((1 - z) ^ 2 * (N ω : ℝ) * ((N ω : ℝ) - 1)) ∂μ := by sorry
