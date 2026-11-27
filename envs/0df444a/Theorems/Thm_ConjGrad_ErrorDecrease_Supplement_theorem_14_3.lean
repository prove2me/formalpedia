-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_14_3
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_14_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:04:58.083161+00:00
-- url     : https://prove2.me/theorems/16c55210-a0f6-4c9e-bbcc-b9fa2da2c497
-- title:
--   Theorem 14:3 — a positive definite $A$ and a vector $r_0$ not perpendicular to any eigenvector have a mass distribution
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix and let $r_0$ be a vector that is not perpendicular to any eigenvector of $A$. Then for every $l$ greater than all eigenvalues of $A$ there is a mass distribution $m(\lambda)$ on $[0,l]$ related to $A$ and $r_0$ as described in §14.
--
--   More precisely, there are ordered eigenvalues $0<\lambda_1<\cdots<\lambda_n<l$, orthonormal eigenvectors $e_j$ and nonzero coefficients $\alpha_j$ with $r_0=\sum_j\alpha_je_j$, for which
--
--   $$\mu=\sum_j \alpha_j^2\,\delta_{\lambda_j}$$
--
--   realizes this correspondence. Thus the construction retains every positive jump prescribed in the proof.
--
--   The theorem makes the correspondence of §14 available for any matrix and generic starting residual, without computing eigenvalues.
--
--   **Formalization Note** `hA.1.eigenvalues` lists the eigenvalues of the symmetric matrix $A$; the mass distribution is a measure as in `IsSpectralModel`.
--
--   Differences from the source:
--   - encoding: $A$ with distinct eigenvalues and $r_0$ not perpendicular to an eigenvector → only the second hypothesis; reason: it implies the first: an eigenspace of dimension $\ge2$ contains a nonzero vector perpendicular to $r_0$; the instances are the same
--   - generalization: “there is a mass distribution” (the proof: $l$ any number greater than $\lambda_n$) → for every $l>\lambda_{\max}$ there is one on $[0,l]$; reason: the existence follows by choosing any such $l$; this is the proof's own construction
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 429, Theorem 14:3 and its proof (choice of $l$) (PDF p. 21)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_IsSpectralModel

open Matrix MeasureTheory

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 14:3 (Hestenes–Stiefel 1952, p. 429): for a positive definite symmetric `A` and a
vector `r₀` not perpendicular to any eigenvector of `A`, and for every `l` exceeding all
eigenvalues of `A`, there is a mass distribution on `[0, l]` related to `A` and `r₀` as in §14. -/
theorem theorem_14_3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (r₀ : Fin n → ℝ)
    (hcyc : ∀ (v : Fin n → ℝ) (c : ℝ), v ≠ 0 → A *ᵥ v = c • v → r₀ ⬝ᵥ v ≠ 0)
    (l : ℝ) (hl : ∀ j, hA.1.eigenvalues j < l) :
    ∃ (lam α : Fin n → ℝ) (e : Fin n → Fin n → ℝ),
      StrictMono lam ∧ (∀ j, 0 < lam j ∧ lam j < l ∧ α j ≠ 0) ∧
      (∀ i j, e i ⬝ᵥ e j = if i = j then 1 else 0) ∧
      (∀ j, A *ᵥ e j = lam j • e j) ∧ r₀ = ∑ j, α j • e j ∧
      IsSpectralModel (∑ j, ENNReal.ofReal (α j ^ 2) • Measure.dirac (lam j)) l A r₀ := by sorry

end ConjGrad.ErrorDecrease.Supplement
