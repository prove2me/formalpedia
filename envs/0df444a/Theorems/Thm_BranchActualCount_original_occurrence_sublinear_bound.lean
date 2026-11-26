-- Prove2me | Theorems.Thm_BranchActualCount_original_occurrence_sublinear_bound
-- name    : BranchActualCount.original_occurrence_sublinear_bound
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T22:32:51.318183+00:00
-- url     : https://prove2.me/theorems/5bc76839-0db9-47de-a645-f93b32bf586e
-- title:
--   Sublinear squared-height bound for the original xi occurrences
-- statement:
--   Let I index the upper-half-plane zeros of ξ with their full multiplicities, and let N(T) count all ζ zeros with 0<Im(s)<T, with multiplicity. Put C=4(N(600)+600). For every y≥1 and every finite set F of occurrences in I whose heights satisfy γᵢ²≤y,
--
--   $$|F|\le C\,y^{3/4}.$$
--
--   This is an unconditional sublinear counting estimate in squared height for the original occurrence index. It does not assert the sharper bound with constant one.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. The new averaging and coarse counting deductions are composed from the analytic formalization of Salvatore Mercuri and Bhavik Mehta in smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, and the pinned PrimeNumberTheoremAnd dependencies. Source copyright headers are retained; Apache-2.0 source license and dependency provenance accompany the reproducibility archive. No mathematical novelty claim. The full original source archive retains both proofs of Gamma_R conjugation. The reduced submission retains the needed declarations with complete proofs and preserves copyright/license headers.

import Mathlib

theorem BranchActualCount.original_occurrence_sublinear_bound :
    let xi : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (s : {s : ℂ // xi s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt xi s.val)
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    ∀ y ≥ (1 : ℝ), ∀ F : Finset I,
      (∀ i ∈ F, i.1.val.im^2 ≤ y) → (F.card : ℝ) ≤ 4*(N 600+600)*y^((3 : ℝ)/4) := by sorry
