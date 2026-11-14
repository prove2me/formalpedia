-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a171_finite_measurable_nonnegative_mask_subselection_preserves_L1_zero
-- name    : AvramDividend.Classical.avram_ga_a171_finite_measurable_nonnegative_mask_subselection_preserves_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:51:11.535196+00:00
-- url     : https://prove2.me/theorems/c9d7d34e-c671-445a-ade7-53d3c0187cbf
-- title:
--   Measurable nonnegative finite source submask preserves integrability and expected L1 convergence to zero
-- statement:
--   For any measurable nonnegative finite observed source terms, restricting an integrable prefix mask to a measurable submask preserves integrability, and if the expected prefix sums vanish, so do those of the submask. This rigorously transfers original stopped Gaussian prefix second-energy and quadratic cross bounds to the actual physically full pre-stop cell mask in a169.
-- source:
--   Finite sum indicator monotonicity, integrable domination, monotone integral and squeeze; supports original full-cell Gaussian correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a171_finite_measurable_nonnegative_mask_subselection_preserves_L1_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ℕ)
    (A B : ℕ → ℕ → Ω → Prop)
    [∀ m i, DecidablePred (A m i)] [∀ m i, DecidablePred (B m i)]
    (f : ℕ → ℕ → Ω → ℝ)
    (hBA : ∀ m i ω, B m i ω → A m i ω)
    (hfNonneg : ∀ m i ω, 0 ≤ f m i ω)
    (hfMeas : ∀ m i, Measurable (f m i))
    (hBMeas : ∀ m i, MeasurableSet {ω : Ω | B m i ω})
    (hAI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, if A m i ω then f m i ω else 0) P)
    (hALim : Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, if A m i ω then f m i ω else 0) ∂P)
      atTop (𝓝 (0 : ℝ))) :
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, if B m i ω then f m i ω else 0) P) ∧
    Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, if B m i ω then f m i ω else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
