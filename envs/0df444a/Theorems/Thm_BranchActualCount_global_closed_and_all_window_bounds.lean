-- Prove2me | Theorems.Thm_BranchActualCount_global_closed_and_all_window_bounds
-- name    : BranchActualCount.global_closed_and_all_window_bounds
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T22:21:12.272785+00:00
-- url     : https://prove2.me/theorems/f5cea25a-c7a3-4b0a-96f1-578315a1a62a
-- title:
--   Global sublinear squared-height count and all-height windows for zeta zeros
-- statement:
--   Let N(T) count all zeta zeros with 0 < Im(rho) < T, with multiplicities, and Nc(T) use 0 < Im(rho) <= T. Unconditionally: (1) for every T >= 1, N(T) <= (N(600)+600) T^(3/2); (2) for every y >= 1, Nc(sqrt(y)) <= 4 (N(600)+600) y^(3/4); (3) for every T >= 1, N(T+1)-N(T) <= (N(601)+50) log(T+3). The constants are explicit expressions in the same finite concrete counting function. They have not been numerically evaluated.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. The new averaging and coarse counting deductions are composed from the analytic formalization of Salvatore Mercuri and Bhavik Mehta in smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, and the pinned PrimeNumberTheoremAnd dependencies. Source copyright headers are retained; Apache-2.0 source license and dependency provenance accompany the reproducibility archive. No mathematical novelty claim. The full original source archive retains both proofs of Gamma_R conjugation. The reduced submission retains the needed declarations with complete proofs and preserves copyright/license headers.

import Mathlib

theorem BranchActualCount.global_closed_and_all_window_bounds :
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    let Nc : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioc 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    (∀ T ≥ (1 : ℝ), N T ≤ (N 600+600)*T^((3 : ℝ)/2)) ∧
    (∀ y ≥ (1 : ℝ), Nc (Real.sqrt y) ≤ 4*(N 600+600)*y^((3 : ℝ)/4)) ∧
    (∀ T ≥ (1 : ℝ), N (T+1)-N T ≤ (N 601+50)*Real.log (T+3)) := by sorry
