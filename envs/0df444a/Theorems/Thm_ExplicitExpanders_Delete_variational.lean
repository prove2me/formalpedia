-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_variational
-- name    : ExplicitExpanders.Delete.variational
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:56:08.217255+00:00
-- url     : https://prove2.me/theorems/e2884983-47cf-4818-85ec-aafc4e705215
-- title:
--   Variational characterization of the nontrivial eigenvalues (Section 2.4)
-- statement:
--   Let $A$ be a real symmetric matrix indexed by a finite set $V$ whose rows all sum to the same number $d$, i.e. $A\mathbf 1 = d\mathbf 1$, and let $\lambda \in \mathbb R$. The following are equivalent:
--
--   1. every eigenvalue $\mu$ of $A$ that has an eigenvector $f\ne 0$ with $\sum_v f(v)=0$ satisfies $|\mu|\le\lambda$;
--   2. for every $f : V\to\mathbb R$ with $\sum_{v} f(v) = 0$,
--   $$|f^{t} A f| \le \lambda \sum_{v\in V} f(v)^2 .$$
--
--   This is the "variational definition of the nontrivial eigenvalues" the paper invokes in Section 2.4 (p. 8) and, under the name "eigenvalue interlacing", for inequality (9) on p. 13. It converts the eigenvalue bound of an $(n,d,\lambda)$-graph into a bound on quadratic forms over functions orthogonal to the constant vector, and back.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 8, Section 2.4 (variational definition of the nontrivial eigenvalues); used for (9), p. 13

import Mathlib

namespace ExplicitExpanders.Delete

open Matrix

/-- The variational definition of the nontrivial eigenvalues (Alon, arXiv:2003.11673v1, §2.4,
p. 8; used for (9) on p. 13). For a real symmetric matrix with constant row sums, all eigenvalues
with an eigenvector orthogonal to the constant vector lie in `[-lam, lam]` iff
`|fᵗ A f| ≤ lam ‖f‖²` for every `f` with `∑ f = 0`. -/
theorem variational {V : Type*} [Fintype V] (A : Matrix V V ℝ) (hA : A.IsSymm) (d : ℝ)
    (hrow : A *ᵥ (fun _ => (1 : ℝ)) = d • (fun _ => (1 : ℝ))) (lam : ℝ) :
    (∀ (μ : ℝ) (f : V → ℝ), f ≠ 0 → ∑ v, f v = 0 → A *ᵥ f = μ • f → |μ| ≤ lam) ↔
      (∀ f : V → ℝ, ∑ v, f v = 0 → |f ⬝ᵥ (A *ᵥ f)| ≤ lam * (f ⬝ᵥ f)) := by sorry

end ExplicitExpanders.Delete
