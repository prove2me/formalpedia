-- Prove2me | Theorems.Thm_ExplicitExpanders_Attach_variational_characterization
-- name    : ExplicitExpanders.Attach.variational_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:13:49.355854+00:00
-- url     : https://prove2.me/theorems/bbb6e0db-a79f-4dae-8ce5-47a8ebbc82dc
-- title:
--   Variational definition of the nontrivial eigenvalues: $|\mu|\le\lambda$ iff $|f^tAf|\le\lambda\|f\|^2$ on $\mathbf 1^\perp$ (Section 2.4)
-- statement:
--   Let $A$ be a real symmetric matrix indexed by a finite set $\iota$ whose rows all sum to the same number $k$, so that $A\mathbf 1=k\mathbf 1$ for the all-ones vector $\mathbf 1$. Let $\lambda\ge 0$. Then the following are equivalent:
--
--   1. every eigenvalue $\mu$ of $A$ that has an eigenvector $f\neq 0$ with $\sum_i f(i)=0$ satisfies $|\mu|\le\lambda$;
--   2. for every real vector $f$ with $\sum_i f(i)=0$,
--   $$|f^{t}Af|\le\lambda\,\|f\|_2^2 .$$
--
--   This is the variational definition of the nontrivial eigenvalues that the paper invokes twice in the proof of Theorem 1.2: from 2 to 1 for the constructed graph $G$, after establishing inequality (1) for all unit vectors orthogonal to $\mathbf 1$; and from 1 to 2 for the Ramanujan graph $H$, to bound $|h^tA_Hh|$ by $2\sqrt p$ for unit vectors $h$ orthogonal to the constant vector.
--
--   **Formalization Note** The paper's normalisation $\|f\|_2^2=1$ is replaced by the homogeneous form $|f^tAf|\le\lambda\, f^tf$, which is equivalent by scaling.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 8, Section 2.4, sentence before (1) (variational definition of the nontrivial eigenvalues); used again on p. 9 for H

import Mathlib

namespace ExplicitExpanders.Attach

open Matrix

/-- Variational definition of the nontrivial eigenvalues (arXiv:2003.11673v1, §2.4, p. 8):
for a real symmetric matrix `A` whose rows all sum to `k` and every `λ ≥ 0`, every eigenvalue of
`A` with an eigenvector orthogonal to the constant vector has absolute value at most `λ` if and
only if `|fᵗ A f| ≤ λ ‖f‖²` for every real vector `f` with `∑ f = 0`. -/
theorem variational_characterization {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (k : ℝ) (hrow : A *ᵥ 1 = k • 1) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∀ (μ : ℝ) (f : ι → ℝ), f ≠ 0 → ∑ i, f i = 0 → A *ᵥ f = μ • f → |μ| ≤ lam) ↔
      (∀ f : ι → ℝ, ∑ i, f i = 0 → |f ⬝ᵥ (A *ᵥ f)| ≤ lam * (f ⬝ᵥ f)) := by sorry

end ExplicitExpanders.Attach
