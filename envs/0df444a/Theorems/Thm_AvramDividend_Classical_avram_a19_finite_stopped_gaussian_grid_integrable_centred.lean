-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_finite_stopped_gaussian_grid_integrable_centred
-- name    : AvramDividend.Classical.avram_a19_finite_stopped_gaussian_grid_integrable_centred
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:44:03.459295+00:00
-- url     : https://prove2.me/theorems/bc24039d-e774-4d36-b50e-626c86fdddad
-- title:
--   Finite original stopped Gaussian grid: integrable centred aggregation
-- statement:
--   For an arbitrary finite set of original predictable stopped Gaussian grid gains, if each gain is integrable and has zero unconditional expectation, their actual finite aggregate is integrable with expectation zero. This is the finite-grid martingale assembly step needed after original stopped Gaussian conditional centring 32d08f0c and before the L1 mesh limit in the original Gaussian finite-cap source e4624500. The lemma does not assert the limiting martingale or HJB cash budget.
-- source:
--   Finite sum Bochner integral and integrability from pinned Mathlib; physical original Gaussian grid use after verified stopped Taylor increment hypotheses.

import Mathlib
open MeasureTheory

/-- Finite aggregation preserves integrability and centring of stopped physical Gaussian gains. -/
theorem AvramDividend.Classical.avram_a19_finite_stopped_gaussian_grid_integrable_centred
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} (s : Finset ι) (G : ι → Ω → ℝ)
    (hInt : ∀ i ∈ s, Integrable (G i) P)
    (hMean : ∀ i ∈ s, (∫ ω, G i ω ∂P) = 0) :
    Integrable (fun ω => ∑ i ∈ s, G i ω) P ∧
    (∫ ω, ∑ i ∈ s, G i ω ∂P) = 0 := by sorry
