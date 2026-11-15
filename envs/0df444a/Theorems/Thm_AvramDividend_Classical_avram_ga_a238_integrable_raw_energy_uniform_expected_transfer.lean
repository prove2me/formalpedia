-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a238_integrable_raw_energy_uniform_expected_transfer
-- name    : AvramDividend.Classical.avram_ga_a238_integrable_raw_energy_uniform_expected_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:08:50.677193+00:00
-- url     : https://prove2.me/theorems/16c7a2ed-eb7e-403e-854b-e9672acce03a
-- title:
--   Finite physical Gaussian raw energy integrable majorant yields uniform expected energy bound
-- statement:
--   For a probability measure, if an integrable raw finite-grid quadratic-energy source F is bounded pointwise by twice an integrable centered source E plus twice a deterministic scalar energy a, and the expected centered source and deterministic energies are uniformly bounded by K and B, the expected raw energy is uniformly at most 2K+2B. Applied to the proved original stopped Gaussian a170, a195 and a237 to support the combined small-cell source a216.
-- source:
--   Original Gaussian stopped full-grid raw energy majorant transfer of a170/a195/a237

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a238_integrable_raw_energy_uniform_expected_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F E : ℕ → Ω → ℝ) (a : ℕ → ℝ) (K B : ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hEBound : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (haBound : ∀ m, a m ≤ B)
    (hPt : ∀ m ω, F m ω ≤ 2 * E m ω + 2 * a m) :
    ∀ m, (∫ ω, F m ω ∂P) ≤ 2 * K + 2 * B := by sorry
