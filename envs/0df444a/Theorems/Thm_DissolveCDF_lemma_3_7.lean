-- Prove2me | Theorems.Thm_DissolveCDF_lemma_3_7
-- name    : DissolveCDF.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:44.43159+00:00
-- url     : https://prove2.me/theorems/cb6f821e-baca-4668-81d9-03a3cf8a609b
-- title:
--   Lemma 3.7 — $J_{\mathcal A}(x)^2=J_{\mathcal A}(x)$ on $\mathcal M$
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   For every $x\in\mathcal M$,
--
--   $$
--   J_{\mathcal A}(x)^2=J_{\mathcal A}(x).
--   $$
--
--   The transposed Jacobian of a constraint dissolving operator is idempotent at feasible points: it is an oblique projection with null space $\mathcal N_x$.
--
--   Differences from the source: none.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Lemma 3.7, p.10

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_transJac

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Lemma 3.7, p.10: for any given `x ∈ M`, `J_A(x)² = J_A(x)`.

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`). -/
theorem lemma_3_7 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A)
    {x : EuclideanSpace ℝ (Fin n)} (hx : c x = 0) :
    transJac A x ∘L transJac A x = transJac A x := by sorry

end DissolveCDF
