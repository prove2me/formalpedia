-- Prove2me | Theorems.Thm_Arxiv1901_08703_inverse_examples_auxiliary_disks_admissible
-- name    : Arxiv1901_08703.inverse_examples_auxiliary_disks_admissible
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:15:49.579877+00:00
-- url     : https://prove2.me/theorems/d2267b85-8603-5801-9e57-d83baeef5d9f
-- title:
--   Section 5.2, assumption 1): $kr$, $k=1,\dots,36$, $r=0.1$, is not a zero of any $J_n$
-- statement:
--   In the inverse-problem examples of Section 5.2, the auxiliary curve $\tilde\Gamma$ is a circle of radius $r=0.1$ and the wave numbers are $k=1,2,\dots,N$ with $N\le36$. For every $k\in\{1,\dots,36\}$ the number $kr=k/10$ is not a zero of any Bessel function $J_n$, $n\in\mathbb Z$. Hence $k^2$ is not a Dirichlet eigenvalue of $-\Delta$ in any disc of radius $0.1$. So the eigenvalue hypothesis of Theorem 2.4 holds for every wave number used, which by Remark 2.5 is the paper's reason why the integral equation (2.14) may be used in all examples.
--
--   **Formalization Note** The statement asserts only the two facts, for every $k\in\{1,\dots,36\}$ and every centre of the disc. It does not assert that the discs lie in $D_R^-$ of the surfaces of Section 5.2, and it does not assert solvability of (2.14).
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c018; Section 5.2, assumption 1) with Remark 2.5, PDF pp. 23-24

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem inverse_examples_auxiliary_disks_admissible :
    ∀ k : ℕ, 1 ≤ k → k ≤ 36 →
      (∀ n : ℤ, besselJ n ((k : ℝ) * (1 / 10)) ≠ 0) ∧
      ∀ c : R2, ¬ IsDirichletEigenvalue (Metric.ball c (1 / 10)) ((k : ℝ) ^ 2) := by sorry

end Arxiv1901_08703
