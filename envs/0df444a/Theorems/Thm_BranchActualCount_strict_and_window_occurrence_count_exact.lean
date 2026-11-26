-- Prove2me | Theorems.Thm_BranchActualCount_strict_and_window_occurrence_count_exact
-- name    : BranchActualCount.strict_and_window_occurrence_count_exact
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T07:34:51.631366+00:00
-- url     : https://prove2.me/theorems/5948113d-9173-4752-97dd-80d0ae1f9634
-- title:
--   Exact strict and half-open window counts for original xi occurrences
-- statement:
--   Index upper-half-plane zeros of ξ with their analytic multiplicities by I. Let N(T) count zeta zeros with 0<Im(ρ)<T and their meromorphic multiplicities. For every real T, the number of occurrences with γ<T equals N(T), and the number with T≤γ<T+1 equals N(T+1)−N(T). No simplicity or RH assumption is made.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. The new averaging and coarse counting deductions are composed from the analytic formalization of Salvatore Mercuri and Bhavik Mehta in smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, and the pinned PrimeNumberTheoremAnd dependencies. Source copyright headers are retained; Apache-2.0 source license and dependency provenance accompany the reproducibility archive. No mathematical novelty claim. The full original source archive retains both proofs of Gamma_R conjugation. The reduced submission retains the needed declarations with complete proofs and preserves copyright/license headers.

import Mathlib

theorem BranchActualCount.strict_and_window_occurrence_count_exact :
    let xi : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (s : {s : ℂ // xi s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt xi s.val)
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    (∀ T : ℝ, (Nat.card {i : I // i.1.val.im < T} : ℝ) = N T) ∧
    (∀ T : ℝ, (Nat.card {i : I // T ≤ i.1.val.im ∧ i.1.val.im < T+1} : ℝ) = N (T+1)-N T) := by sorry
