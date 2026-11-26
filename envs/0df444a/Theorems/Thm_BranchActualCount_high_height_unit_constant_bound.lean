-- Prove2me | Theorems.Thm_BranchActualCount_high_height_unit_constant_bound
-- name    : BranchActualCount.high_height_unit_constant_bound
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T11:48:57.852205+00:00
-- url     : https://prove2.me/theorems/46efebc0-2bbb-4657-8fb0-aa1647b29860
-- title:
--   Zeta zero count with unit constant for all heights at least 1000
-- statement:
--   Let N(H) count all Riemann zeta zeros with 0<Im(s)<H, counted with multiplicity. For every real T≥1000, N(T+1)≤T sqrt(T). The shift covers every zero on the closed height boundary T. This theorem is unconditional and does not assert the bound below 1000 or global RH.
-- source:
--   Analytic lemmas from smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033 and PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe. Apache-2.0 authorship headers preserved in the proof. Explicit high-height unit-constant estimate and Lean composition by Desenvolvimento RH, coordinated by Ricardo Marangoni Brandão Bueno.

import Mathlib

theorem BranchActualCount.high_height_unit_constant_bound :
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    ∀ T ≥ (1000 : ℝ), N (T+1) ≤ T*Real.sqrt T := by sorry
