-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_finite_simple_rectangle_compensation
-- name    : AvramDividend.Classical.avram_p2_f_weighted_finite_simple_rectangle_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:12:16.755594+00:00
-- url     : https://prove2.me/theorems/ff4ce462-4081-4f3f-b3c7-ed3c1dfb13d4
-- title:
--   Finite predictable rectangle sums obey exact nonnegative compensation from event rates
-- statement:
--   For a finite family of nonnegative measurable original random counts N_i and past-measurable weights H_i, suppose each count has the exact event rectangle moment μ(A)*r_i on all past events. Then the lintegral of the finite sum of weighted counts equals the finite sum of expected weights multiplied by their rates. No independence, finite expectation, sigma-finiteness or ν-rate is assumed. Nonnegative finite-sum linearity and the separately proved event-to-general ENNReal-weight transfer handle 0*∞ correctly. This is a useful finite predictable-step compensation interface for original Lévy jump measures after the genuine rates are independently proved.
-- source:
--   Mathematically independent finite-simple closure of P2-F generic indicator-to-weight theorem 086b5c5f and pinned MeasureTheory.lintegral_finset_sum. Useful to W7-06 and downstream P2-E simple predictable integration, without submitting canonical targets or assuming original ν.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_finite_simple_rectangle_compensation
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (mPast : MeasurableSpace Ω) (hm : mPast ≤ mΩ)
    (μ : Measure Ω) (S : Finset ι)
    (N H : ι → Ω → ℝ≥0∞) (r : ι → ℝ≥0∞)
    (hN : ∀ i ∈ S, Measurable (N i))
    (hH : ∀ i ∈ S, Measurable[mPast] (H i))
    (hEvent : ∀ i ∈ S, ∀ A : Set Ω, MeasurableSet[mPast] A →
      (∫⁻ ω in A, N i ω ∂μ) = μ A * r i) :
    (∫⁻ ω, S.sum (fun i => H i ω * N i ω) ∂μ) =
    S.sum (fun i => (∫⁻ ω, H i ω ∂μ) * r i) := by sorry
