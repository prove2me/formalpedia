-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a58_true_stop_positive_taylor_expected_energy_split
-- name    : AvramDividend.Classical.avram_ga_a58_true_stop_positive_taylor_expected_energy_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:14:19.561205+00:00
-- url     : https://prove2.me/theorems/821d56fb-5201-4427-bfb2-55ebf9e4009c
-- title:
--   Original true stopped Gaussian positive Taylor expectation bounded by total source energy and rare large-cell energy
-- statement:
--   Under positive remainder coefficient bounds on each physical cell strictly before the true stopping clock and integrability of the three finite energies, the expected positive Taylor quadratic remainder is bounded by a small fixed fraction of total expected energy plus a fixed multiple of expected rare large-increment energy.
-- source:
--   Integrates proved ga_a44 for original b0d9951c compact positive spatial Taylor. Next combine with ga_a39 and ga_a56.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a58_true_stop_positive_taylor_expected_energy_split
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ι) (s : ι → ℝ≥0) (ρ : Ω → ℝ≥0)
    (a z : ι → Ω → ℝ) (ε M δ : ℝ)
    (hε : 0 ≤ ε)
    (ha : ∀ ω : Ω, ∀ i ∈ S, s i < ρ ω → 0 ≤ a i ω)
    (hM : ∀ ω : Ω, ∀ i ∈ S, s i < ρ ω → a i ω ≤ M)
    (hSmall : ∀ ω : Ω, ∀ i ∈ S, s i < ρ ω →
      |z i ω| < δ → a i ω ≤ ε) :
    let A : Ω → ℝ := fun ω =>
      ∑ i ∈ S, if s i < ρ ω then a i ω * (z i ω)^2 else 0
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, if s i < ρ ω then (z i ω)^2 else 0
    let T : Ω → ℝ := fun ω =>
      ∑ i ∈ S, if s i < ρ ω then
        (if δ ≤ |z i ω| then (z i ω)^2 else 0) else 0
    Integrable A P → Integrable E P → Integrable T P →
      (∫ ω, A ω ∂P) ≤ ε * (∫ ω, E ω ∂P) +
        M * (∫ ω, T ω ∂P) := by sorry
