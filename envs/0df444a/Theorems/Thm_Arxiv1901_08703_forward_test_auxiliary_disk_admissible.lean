-- Prove2me | Theorems.Thm_Arxiv1901_08703_forward_test_auxiliary_disk_admissible
-- name    : Arxiv1901_08703.forward_test_auxiliary_disk_admissible
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:09:37.791319+00:00
-- url     : https://prove2.me/theorems/cda7e304-1650-4391-a173-d0b3e7151cf6
-- title:
--   Section 3.2, item 2): $k=100$, $r=0.1$ satisfies the hypothesis of Theorem 2.4
-- statement:
--   For the numerical test of Section 3.2, the auxiliary curve is the boundary of the disc $\tilde D$ of radius $r=0.1$ centred at $(0,-0.5)$, and the wave number is $k=100$. Then $kr=10$ is not a zero of any Bessel function $J_n$, $n\in\mathbb Z$, and $k^2=10^4$ is not a Dirichlet eigenvalue of $-\Delta$ in $\tilde D$. So the eigenvalue hypothesis of Theorem 2.4 holds for this disc, which by Remark 2.5 is the paper's reason why the integral equation (2.14) may be used.
--
--   **Formalization Note** The statement asserts only the two facts (no $J_n$ vanishes at $10$; $10^4$ is not a Dirichlet eigenvalue of this disc). It does not check the other hypothesis of Theorem 2.4, $\overline{\tilde D}\subset D_R^-$ for the test surface, and it does not assert solvability of (2.14).
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c012; Section 3.2, parameter item 2) with Remark 2.5, PDF p. 17

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem forward_test_auxiliary_disk_admissible :
    (∀ n : ℤ, besselJ n ((100 : ℝ) * (1 / 10)) ≠ 0) ∧
    ¬ IsDirichletEigenvalue (Metric.ball (pt 0 (-1 / 2)) (1 / 10)) ((100 : ℝ) ^ 2) := by sorry

end Arxiv1901_08703
