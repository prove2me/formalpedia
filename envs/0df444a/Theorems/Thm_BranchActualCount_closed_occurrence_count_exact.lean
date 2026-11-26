-- Prove2me | Theorems.Thm_BranchActualCount_closed_occurrence_count_exact
-- name    : BranchActualCount.closed_occurrence_count_exact
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T22:27:25.500788+00:00
-- url     : https://prove2.me/theorems/76982e18-3513-4a0d-bb64-162f97aec998
-- title:
--   Exact closed-height zero count for the original xi occurrence index
-- statement:
--   Let ξ(s)=(1+s(s−1)Λ₀(s))/2, where Λ₀ is the entire part of the completed Riemann zeta function. Index every zero of ξ in the upper half-plane by its analytic multiplicity, forming the occurrence set I. Let Nc(T) count the zeros of ζ with 0<Im(s)≤T, with meromorphic multiplicity. For every real T, the number of occurrences in I with height at most T equals Nc(T). Consequently, any finite collection F of such occurrences has cardinality at most Nc(T). The claim includes the boundary height and does not assume simple zeros or RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. The new averaging and coarse counting deductions are composed from the analytic formalization of Salvatore Mercuri and Bhavik Mehta in smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, and the pinned PrimeNumberTheoremAnd dependencies. Source copyright headers are retained; Apache-2.0 source license and dependency provenance accompany the reproducibility archive. No mathematical novelty claim. The full original source archive retains both proofs of Gamma_R conjugation. The reduced submission retains the needed declarations with complete proofs and preserves copyright/license headers.

import Mathlib

theorem BranchActualCount.closed_occurrence_count_exact :
    let xi : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (s : {s : ℂ // xi s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt xi s.val)
    let Nc : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioc 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    (∀ T : ℝ, (Nat.card {i : I // i.1.val.im ≤ T} : ℝ) = Nc T) ∧
    (∀ T : ℝ, ∀ F : Finset I, (∀ i ∈ F, i.1.val.im ≤ T) → (F.card : ℝ) ≤ Nc T) := by sorry
