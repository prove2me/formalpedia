-- Prove2me | Theorems.Thm_BranchActualCount_concrete_zero_count_bounds
-- name    : BranchActualCount.concrete_zero_count_bounds
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T17:28:31.450903+00:00
-- url     : https://prove2.me/theorems/95824c54-2c5f-4ea8-a641-fe633190d7dc
-- title:
--   Concrete logarithmic window bound and positive lower density for zeta zeros
-- statement:
--   Let N(T) count the zeros of the Riemann zeta function with imaginary part strictly between 0 and T, counted with their meromorphic multiplicities. Then, for every real T ≥ 600,
--   \[N(T+1)-N(T)\le 50\log(T+3).\]
--   Moreover, for all sufficiently large real T,
--   \[N(T)\ge \frac{T\log T}{32\pi}.\]
--   Both estimates are unconditional. The strict upper-height convention makes the difference count the half-open interval [T,T+1), including multiplicities. This theorem supplies quantitative counting inputs for a separate spectral positivity argument; it does not assert RH or the complete Branches.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. The new averaging and coarse counting deductions are composed from the analytic formalization of Salvatore Mercuri and Bhavik Mehta in smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, and the pinned PrimeNumberTheoremAnd dependencies. Source copyright headers are retained; Apache-2.0 source license and dependency provenance accompany the reproducibility archive. No mathematical novelty claim. Both source proofs of Gamma_R conjugation are retained; one duplicate declaration is renamed for the single-file port.

import Mathlib

theorem BranchActualCount.concrete_zero_count_bounds :
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    (∀ T ≥ (600 : ℝ), N (T+1)-N T ≤ 50*Real.log (T+3)) ∧
    (∀ᶠ T : ℝ in Filter.atTop, T*Real.log T/(32*Real.pi) ≤ N T) := by sorry
