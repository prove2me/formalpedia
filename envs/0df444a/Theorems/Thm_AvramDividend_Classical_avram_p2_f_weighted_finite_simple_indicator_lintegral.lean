-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_finite_simple_indicator_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_finite_simple_indicator_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:29:16.378726+00:00
-- url     : https://prove2.me/theorems/5abd0ce8-11c2-44fb-863f-9bf8eafce612
-- title:
--   Exact finite simple nonnegative marked-cell lintegral equals sum of weighted source measure masses
-- statement:
--   For a finite collection of measurable marked cells, possibly overlapping, and arbitrary nonnegative ENNReal simple weights, the integral of the sum of weighted cell indicators with respect to any actual measure equals the sum of the weights times the measure's true cell masses. It uses exact ENNReal addition including zero/infinity and requires no disjointness. Specialising the measure to the original intrinsic Lévy jump measure gives the deterministic pathwise simple predictable integrand identity required before taking outer expectation and applying P2-F/P2-E marked-cell rates.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_finset_sum, lintegral_indicator and constant lintegral.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_finite_simple_indicator_lintegral
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι)
    (C : ι → Set α) (hC : ∀ i ∈ S, MeasurableSet (C i))
    (w : ι → ℝ≥0∞) :
    (∫⁻ x, S.sum (fun i => (C i).indicator (fun _ => w i) x) ∂μ) =
    S.sum (fun i => w i * μ (C i)) := by sorry
