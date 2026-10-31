-- Prove2me | Theorems.Thm_DissolveCDF_lemma_3_5
-- name    : DissolveCDF.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:52.220735+00:00
-- url     : https://prove2.me/theorems/21dc9d87-e74a-4e59-ba66-64557df7d536
-- title:
--   Lemma 3.5 — $J_{\mathcal A}(x)^\top d\in\mathcal T_x$, and $J_{\mathcal A}(x)^\top d=d$ for $d\in\mathcal T_x$
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   Let $x\in\mathcal M$ and let $\mathcal T_x=\{d\in\mathbb R^n: d^\top J_c(x)=0\}=\operatorname{Null}(J_c(x)^\top)$ be the tangent space of $\mathcal M$ at $x$. Then
--
--   1. $J_{\mathcal A}(x)^\top d\in\mathcal T_x$ for every $d\in\mathbb R^n$;
--   2. $J_{\mathcal A}(x)^\top d=d$ for every $d\in\mathcal T_x$.
--
--   So $J_{\mathcal A}(x)^\top=D\mathcal A(x)$ is a projection onto the tangent space at feasible points.
--
--   **Formalization Note** $J_{\mathcal A}(x)^\top$ and $J_c(x)^\top$ are the adjoints of the transposed Jacobians, and $d\in\mathcal T_x$ is written $J_c(x)^\top d=0$.
--
--   Differences from the source: none.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Lemma 3.5, p.10

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_transJac

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Lemma 3.5, p.10: for any given `x ∈ M`, `J_A(x)ᵀ d ∈ T_x` for any `d ∈ ℝⁿ`;
moreover, when `d ∈ T_x`, `J_A(x)ᵀ d = d`. Here `T_x := {d : dᵀJ_c(x) = 0} = Null(J_c(x)ᵀ)` (p.5).

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`). **Formalization Note** `J_A(x)ᵀ` and `J_c(x)ᵀ` are the adjoints of the transposed
Jacobians (i.e. the Fréchet derivatives `DA(x)`, `Dc(x)`); `d ∈ T_x` is `J_c(x)ᵀ d = 0`. -/
theorem lemma_3_5 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A)
    {x : EuclideanSpace ℝ (Fin n)} (hx : c x = 0) :
    (∀ d : EuclideanSpace ℝ (Fin n),
        ContinuousLinearMap.adjoint (transJac c x) (ContinuousLinearMap.adjoint (transJac A x) d) = 0) ∧
      (∀ d : EuclideanSpace ℝ (Fin n), ContinuousLinearMap.adjoint (transJac c x) d = 0 →
        ContinuousLinearMap.adjoint (transJac A x) d = d) := by sorry

end DissolveCDF
