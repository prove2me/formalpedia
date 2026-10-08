-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_eq_9
-- name    : ExplicitExpanders.Delete.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:16:02.159356+00:00
-- url     : https://prove2.me/theorems/9fab0250-c209-4b11-b6c5-b7877801f97b
-- title:
--   Inequality (9) — $|f^tA_{H'}f| \le \lambda\|f\|^2$ for $f\perp\mathbf 1$ on $V\setminus U$
-- statement:
--   Let $H$ be an $(n,d,\lambda)$-graph on $V$, let $U \subseteq V$, and let $H'$ be the subgraph of $H$ induced on $V\setminus U$, with adjacency matrix $A_{H'}$. Then for every $f : V\setminus U \to \mathbb R$ with $\sum_{x} f(x) = 0$,
--   $$|f^{t}A_{H'}f| \le \lambda \sum_{x\in V\setminus U} f(x)^2 . \tag{9}$$
--
--   In the paper (p. 13), $\lambda = 2\sqrt{d-1}+\varepsilon/2$ and $f$ is a unit eigenvector of $G$ for a nontrivial eigenvalue, so (9) reads $|f^tA_{H'}f| \le 2\sqrt{d-1}+\varepsilon/2$. The paper justifies it "by eigenvalue interlacing", since $H'$ is an induced subgraph of $H$. The item states it for every $\lambda$ and every $f$ orthogonal to the constant vector, which contains the paper's case.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 13, inequality (9)

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

namespace ExplicitExpanders.Delete

open Matrix

open Classical in
/-- (9) (Alon, arXiv:2003.11673v1, p. 13): if `H` is an `(n, d, lam)`-graph, then for every
function `f` on `V ∖ U` with `∑ f = 0`, `|fᵗ A_{H'} f| ≤ lam ‖f‖²`, where `H'` is the subgraph
induced on `V ∖ U`. -/
theorem eq_9 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (n d : ℕ) (lam : ℝ)
    (hH : IsNDLambda H n d lam) (U : Finset V) (f : Kept U → ℝ) (hf : ∑ x, f x = 0) :
    |f ⬝ᵥ ((deleted H U).adjMatrix ℝ *ᵥ f)| ≤ lam * ∑ x, f x ^ 2 := by sorry

end ExplicitExpanders.Delete
