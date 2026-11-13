-- Prove2me | Theorems.Thm_DeepQOperator_spectral_tail
-- name    : DeepQOperator.spectral_tail
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:00:10.184306+00:00
-- url     : https://prove2.me/theorems/d9a1884a-8416-408e-9b93-944d33d8aafa
-- title:
--   K.3: a projector of rank at most $N$ leaves the spectral tail $\sum_{k>N}\lambda_k$
-- statement:
--   1. If $\operatorname{rank}M\le N$ and $\Pi$ is the orthogonal projector onto $\ker M$, then $I-\Pi$ is a projector of rank at most $N$.
--   2. Let $B$ be symmetric positive semidefinite with eigenvalues $\lambda_1\ge\dots\ge\lambda_d\ge0$, and let $\Pi$ be an orthogonal projector with $\operatorname{rank}(I-\Pi)\le N$. Then
--   $$\operatorname{tr}\big((I-\Pi)B\big)\le\sum_{k=1}^N\lambda_k,\qquad\operatorname{tr}(\Pi B)\ge\sum_{k>N}\lambda_k.$$
--   For $N\ge d$ the latter sum is zero.
--
--   With $M=CI^{-1/2}$ and $B$ the boundary matrix (22), this turns (69)–(70) into the spectral lower bound of Theorem 6.
--
--   **Formalization Note** Orthogonal projectors are symmetric idempotent real matrices; "onto $\ker M$" is $M\Pi=0$ and $\Pi x=x$ on $\ker M$. Eigenvalues are indexed from $0$ in decreasing order, so $k\le N$ becomes $k<N$ and $k>N$ becomes $k\ge N$.
--
--   Differences from the source:
--   - generalization: Π_C, the projector onto ker(CI^{−1/2}), and B of (22) → any real matrix M, any orthogonal projector Π, any symmetric positive semidefinite B; reason: the paper's objects are instances
--   - encoding: λ_1 ≥ ⋯ ≥ λ_d, tail k > N → eigenvalues₀ indexed from 0, tail N ≤ k; reason: index shift by one
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix K.3, p.40 (PDF p.43)

import Mathlib

open Matrix

namespace DeepQOperator

/-- **The spectral tail** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix K.3, p.40, PDF p.43).

If `rank C ≤ N`, then `I - Π_C` is a projector of rank at most `N`, where `Π_C` is the orthogonal
projector onto `ker C`. For a symmetric positive semidefinite `B` with eigenvalues
`λ₁ ≥ ⋯ ≥ λ_d ≥ 0` and an orthogonal projector `Π` with `rank(I - Π) ≤ N`:
`tr((I - Π)B) ≤ Σ_{k=1}^N λ_k` and `tr(ΠB) ≥ Σ_{k>N} λ_k`. For `N ≥ d` the latter sum is zero.

**Formalization Note.** Orthogonal projectors are real symmetric idempotent matrices. The first
clause takes any real matrix `M` (in the paper `C I^{-1/2}`) and a projector `Π` onto `ker M`
(`MΠ = 0` and `Πx = x` on `ker M`); its conclusion is that `I - Π` is an orthogonal projector
(symmetric and idempotent) of rank at most `N`. Eigenvalues are `eigenvalues₀`, indexed from `0` in decreasing order,
so the paper's `k ≤ N` is `k.val < N` and `k > N` is `N ≤ k.val`; for `N ≥ d` the second index set is
empty. -/
theorem spectral_tail {d N : ℕ} (B Pi : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef)
    (hPh : Pi.IsHermitian) (hPi : Pi * Pi = Pi) :
    (∀ {k : ℕ} (M : Matrix (Fin k) (Fin d) ℝ), M.rank ≤ N → (∀ x, M *ᵥ (Pi *ᵥ x) = 0) →
      (∀ x, M *ᵥ x = 0 → Pi *ᵥ x = x) →
        (1 - Pi).IsHermitian ∧ (1 - Pi) * (1 - Pi) = 1 - Pi ∧ (1 - Pi).rank ≤ N) ∧
    ((1 - Pi).rank ≤ N →
      ((1 - Pi) * B).trace ≤
          ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card (Fin d)) => k.val < N),
            hB.isHermitian.eigenvalues₀ k ∧
        ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card (Fin d)) => N ≤ k.val),
            hB.isHermitian.eigenvalues₀ k ≤ (Pi * B).trace) := by sorry

end DeepQOperator
