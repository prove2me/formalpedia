-- Prove2me | Theorems.Thm_DiscreteChoiceProx_Simplex_lemma_5
-- name    : DiscreteChoiceProx.Simplex.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:06.259199+00:00
-- url     : https://prove2.me/theorems/335ee019-fbd6-41ab-ba09-f334b681fe99
-- title:
--   Lemma 5 — matrix induced norm bounded by twice the trace
-- statement:
--   Let $A$ be a symmetric real matrix in the paper's class $\mathcal A$: its diagonal entries are nonnegative, off-diagonal entries are nonpositive, and each row sums to zero. Then
--
--   $$
--   \|A\|_{\infty,1}\le 2\operatorname{tr}(A).
--   $$
--
--   Here $\|A\|_{\infty,1}=\max_{\|z\|_\infty\le1}\|Az\|_1$. The bound is the matrix estimate used in the proof of Theorem 2. It is stated for every such finite matrix, independently of any random utility law.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, p. 11, Lemma 5

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

namespace DiscreteChoiceProx.Simplex

/-- Lemma 5, p. 11: the induced norm of a matrix in `𝒜`. -/
theorem lemma_5 {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : ClassA A) :
    normInfOne A ≤ 2 * A.trace := by sorry

end DiscreteChoiceProx.Simplex
