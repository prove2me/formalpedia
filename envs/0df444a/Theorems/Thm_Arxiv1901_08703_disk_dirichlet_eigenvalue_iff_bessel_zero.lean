-- Prove2me | Theorems.Thm_Arxiv1901_08703_disk_dirichlet_eigenvalue_iff_bessel_zero
-- name    : Arxiv1901_08703.disk_dirichlet_eigenvalue_iff_bessel_zero
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:40:52.369431+00:00
-- url     : https://prove2.me/theorems/73d94c68-766d-4f78-8781-bb66ee0cee5a
-- title:
--   Remark 2.5: Dirichlet eigenvalues of a disc and zeros of $J_n$
-- statement:
--   Let $k>0$ and let $\tilde D=B_r(c)$ be a disc of radius $r>0$. Then:
--
--   1. $k^2$ is a Dirichlet eigenvalue of $-\Delta$ in $\tilde D$ if and only if $kr$ is a zero of the Bessel function $J_n$ for some integer $n$;
--   2. if $kr$ is smaller than the smallest positive zero $j_{0,1}$ of $J_0$, then $k^2$ is not a Dirichlet eigenvalue of $-\Delta$ in $\tilde D$.
--
--   **Formalization Note** For $n<0$, $J_n=(-1)^nJ_{|n|}$. The smallest zero of $J_0$ is written as $\inf\{x>0:J_0(x)=0\}$. Part 2 needs the fact, not stated in the paper, that $j_{0,1}$ is smaller than every positive zero of every $J_n$.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c020; Section 2, Remark 2.5, PDF p. 13

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem disk_dirichlet_eigenvalue_iff_bessel_zero (k : ℝ) (hk : 0 < k) (c : R2) (r : ℝ)
    (hr : 0 < r) :
    (IsDirichletEigenvalue (Metric.ball c r) (k ^ 2) ↔ ∃ n : ℤ, besselJ n (k * r) = 0) ∧
    (k * r < sInf {x : ℝ | 0 < x ∧ besselJ 0 x = 0} →
      ¬ IsDirichletEigenvalue (Metric.ball c r) (k ^ 2)) := by sorry

end Arxiv1901_08703
