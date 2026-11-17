-- Prove2me | Theorems.Thm_BranchActualCount_unit_window_bound
-- name    : BranchActualCount.unit_window_bound
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T18:03:46.006664+00:00
-- url     : https://prove2.me/theorems/d79a5c27-fe7b-416c-9aa8-8d90f8f4b050
-- title:
--   Logarithmic bound for zeta zeros in a unit height window
-- statement:
--   Let $N(T)$ count the zeros of the Riemann zeta function with $0<\operatorname{Im}\rho<T$, with meromorphic multiplicities. For every real $T\ge600$,
--
--   $$N(T+1)-N(T)\le50\log(T+3).$$
--
--   The difference counts the half-open height interval $[T,T+1)$. This unconditional local counting estimate is an input to spectral summation estimates.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. The new averaging and coarse counting deductions are composed from the analytic formalization of Salvatore Mercuri and Bhavik Mehta in smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, and the pinned PrimeNumberTheoremAnd dependencies. Source copyright headers are retained; Apache-2.0 source license and dependency provenance accompany the reproducibility archive. No mathematical novelty claim. The full original source archive retains both proofs of Gamma_R conjugation. The reduced submission retains the needed declarations with complete proofs and preserves copyright/license headers.

import Mathlib

theorem BranchActualCount.unit_window_bound :
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    ∀ T ≥ (600 : ℝ), N (T+1)-N T ≤ 50*Real.log (T+3) := by sorry
