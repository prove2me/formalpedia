-- Prove2me | Theorems.Thm_DiscreteChoiceProx_Simplex_lemma_3
-- name    : DiscreteChoiceProx.Simplex.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:40.585159+00:00
-- url     : https://prove2.me/theorems/ffa5fec6-1786-49f1-8885-8122dd32fd30
-- title:
--   Lemma 3 — Hessian norm criterion for smoothness
-- statement:
--   Let $L>0$. If the induced norm from $\ell_\infty$ to $\ell_1$ of the surplus Hessian is at most $L$ at every utility vector, then $E$ is $L$-strongly smooth in the maximum norm:
--
--   $$
--   \bigl(\forall u\in\mathbb R^n,\ \|\nabla^2 E(u)\|_{\infty,1}\le L\bigr)
--   \Longrightarrow
--   E(u+v)\le E(u)+\langle\nabla E(u),v\rangle+\frac L2\|v\|_\infty^2.
--   $$
--
--   This is the paper's criterion that links a matrix estimate to its surplus smoothness claim.
--
--   **Formalization Note** The statement explicitly assumes $E$ is twice continuously differentiable. Page 7 uses twice differentiability as a fact, although Assumption 1 alone does not guarantee it.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, p. 8, Lemma 3

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

open MeasureTheory

namespace DiscreteChoiceProx.Simplex

/-- Lemma 3, p. 8: a Hessian norm bound gives strong smoothness. -/
theorem lemma_3 {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hA : Assumption1 μ)
    (hE : ContDiff ℝ 2 (surplus μ)) (L : ℝ) (hL : 0 < L)
    (hbound : ∀ u, normInfOne (hess (surplus μ) u) ≤ L) :
    IsStronglySmoothSup (surplus μ) L := by sorry

end DiscreteChoiceProx.Simplex
