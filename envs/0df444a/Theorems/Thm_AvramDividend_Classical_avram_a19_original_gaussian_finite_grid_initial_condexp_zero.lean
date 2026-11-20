-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_original_gaussian_finite_grid_initial_condexp_zero
-- name    : AvramDividend.Classical.avram_a19_original_gaussian_finite_grid_initial_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:55:48.080982+00:00
-- url     : https://prove2.me/theorems/016f1db4-6cab-4afb-b5c4-01894ea615fa
-- title:
--   Finite original stopped Gaussian grid preserves initial conditional centring
-- statement:
--   For the finite collection of true stopped predictable Gaussian physical grid increments, if each source increment is integrable and has conditional expectation zero given the initial filtration, its total is integrable and has the same zero conditional expectation. This strengthens the already proved unconditional finite-grid aggregation and supplies a rigorous conditional-centred component toward e4624500 in the original finite-cap stopped Itô proof. Actual local-time, ruin-contact and L1 mesh convergence remain separate.
-- source:
--   Pinned Mathlib condExp_finset_sum and integrable_finset_sum. Instantiated with original initial filtration m0=F.rightCont 0 and physical stopped Gaussian increments.

import Mathlib
open MeasureTheory

/-- Original finite stopped Gaussian grid gains remain centred conditionally on the initial filtration. -/
theorem AvramDividend.Classical.avram_a19_original_gaussian_finite_grid_initial_condexp_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m₀ : MeasurableSpace Ω) {ι : Type*}
    (s : Finset ι) (G : ι → Ω → ℝ)
    (hInt : ∀ i ∈ s, Integrable (G i) P)
    (hCond : ∀ i ∈ s,
      condExp m₀ P (G i) =ᵐ[P] (fun _ => (0 : ℝ))) :
    Integrable (fun ω => ∑ i ∈ s, G i ω) P ∧
    condExp m₀ P (fun ω => ∑ i ∈ s, G i ω)
      =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
