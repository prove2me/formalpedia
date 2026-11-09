-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_theorem_2_1
-- name    : BLTCounting.AccuracySpace.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:48.256492+00:00
-- url     : https://prove2.me/theorems/4b0e2ef7-ae23-49ad-989d-cd52b93bfce7
-- title:
--   Courant–Fischer min–max for complex Hermitian matrices
-- statement:
--   Let $A\in\mathbb C^{K\times K}$ be Hermitian, with eigenvalues $\lambda_1(A)\ge\dots\ge\lambda_K(A)$. For every $1\le q\le K$,
--   $$\lambda_q(A)=\max_{\substack{U\subseteq\mathbb C^K\\ \dim U=q}}\ \min_{\substack{u\in U\\ u\neq0}}\frac{u^*Au}{\|u\|_2^2}.$$
--   In particular, if a $q$-dimensional subspace $U$ satisfies $u^*Au\ge\alpha\|u\|_2^2$ for every $u\in U$, then $\lambda_j(A)\ge\alpha$ for $1\le j\le q$.
--
--   This turns a quadratic-form bound on a subspace into a count of large eigenvalues.
--
--   **Formalization Note.** Maximum and minimum are stated as attained, with `IsGreatest` and `IsLeast`. `eigAt hA (q - 1)` is $\lambda_q(A)$; the subtraction is applied only to $q\ge1$.
--
--   Differences from the source: none.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Theorem 2.1, printed p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms

open Matrix

namespace BLTCounting.AccuracySpace

/-- Theorem 2.1 (Courant–Fischer), PDF p. 11: for Hermitian `A ∈ ℂ^{K×K}` and `1 ≤ q ≤ K`,
`λ_q(A) = max_{dim U = q} min_{0 ≠ u ∈ U} u* A u / ‖u‖₂²` (`eigAt` is zero-indexed), and if a
`q`-dimensional subspace `U` satisfies `u* A u ≥ α ‖u‖₂²` on `U`, then `λ_j(A) ≥ α` for `1 ≤ j ≤ q`. -/
theorem theorem_2_1 (K : ℕ) (A : Matrix (Fin K) (Fin K) ℂ) (hA : A.IsHermitian) :
    (∀ q : ℕ, 1 ≤ q → q ≤ K →
      IsGreatest
        {v : ℝ | ∃ U : Submodule ℂ (Fin K → ℂ), Module.finrank ℂ U = q ∧
          IsLeast (rayleigh A '' {u | u ∈ U ∧ u ≠ 0}) v}
        (eigAt hA (q - 1))) ∧
      ∀ (q : ℕ) (α : ℝ) (U : Submodule ℂ (Fin K → ℂ)), Module.finrank ℂ U = q →
        (∀ u ∈ U, α * euclSq u ≤ (star u ⬝ᵥ (A *ᵥ u)).re) →
        ∀ j : ℕ, 1 ≤ j → j ≤ q → α ≤ eigAt hA (j - 1) := by sorry

end BLTCounting.AccuracySpace
