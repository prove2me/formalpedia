-- Prove2me | Theorems.Thm_DissolveCDF_lemma_3_6
-- name    : DissolveCDF.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:52.880599+00:00
-- url     : https://prove2.me/theorems/2d142fb8-fa81-4829-a5bc-94bbb7e9ff8f
-- title:
--   Lemma 3.6 — $J_{\mathcal A}(x)d=0$ iff $d\in\mathcal N_x$
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   Let $x\in\mathcal M$ and let $\mathcal N_x=\{d: d^\top u=0\ \forall u\in\mathcal T_x\}=\operatorname{range}(J_c(x))$ be the normal space of $\mathcal M$ at $x$. Then for every $d\in\mathbb R^n$,
--
--   $$
--   J_{\mathcal A}(x)\,d=0\iff d\in\mathcal N_x .
--   $$
--
--   **Formalization Note** $d\in\mathcal N_x$ is written $d=J_c(x)\nu$ for some $\nu\in\mathbb R^p$, the description $\mathcal N_x=\operatorname{range}(J_c(x))$ the paper gives on p.5.
--
--   Differences from the source: none.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Lemma 3.6, p.10 (N_x from §2.1, p.5)

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_transJac

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Lemma 3.6, p.10: for any given `x ∈ M`, `J_A(x) d = 0` holds if and only if
`d ∈ N_x`, where `N_x := {d : dᵀu = 0 ∀ u ∈ T_x} = range(J_c(x))` (p.5).

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`). **Formalization Note** `d ∈ N_x` is written as `d = J_c(x)ν` for some `ν ∈ ℝᵖ` (the range of `J_c(x)`),
the second of the paper's two descriptions of it (p.5). -/
theorem lemma_3_6 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A)
    {x : EuclideanSpace ℝ (Fin n)} (hx : c x = 0) (d : EuclideanSpace ℝ (Fin n)) :
    transJac A x d = 0 ↔ ∃ ν : EuclideanSpace ℝ (Fin p), transJac c x ν = d := by sorry

end DissolveCDF
