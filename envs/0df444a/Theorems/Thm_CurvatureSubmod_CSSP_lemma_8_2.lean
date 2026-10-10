-- Prove2me | Theorems.Thm_CurvatureSubmod_CSSP_lemma_8_2
-- name    : CurvatureSubmod.CSSP.lemma_8_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:00.362118+00:00
-- url     : https://prove2.me/theorems/3573da30-c8f7-4a63-a8f5-9fd8900dbfd5
-- title:
--   Lemma 8.2, p. 11 — for A with independent columns, f^A has total curvature at most 1 − 1/κ²(A)
-- statement:
--   Let $A$ be a real $m \times n$ matrix whose columns $c_1, \dots, c_n \in \mathbb{R}^m$ are linearly independent, and let
--   $$\kappa(A) = \frac{\sup_{\|x\|=1}\|Ax\|}{\inf_{\|x\|=1}\|Ax\|}$$
--   be its condition number. Let $f^A(S) = \sum_{i=1}^n \|c_i - \mathrm{proj}_S(c_i)\|^2$ be the column-subset selection objective, a monotone decreasing set function on $[n]$. Then $f^A$ has total curvature at most $1 - 1/\kappa^2(A)$:
--   $$f^A_{[n]-j}(j) \le \frac{1}{\kappa^2(A)}\, f^A_\emptyset(j) \qquad \text{for every } j \in [n].$$
--
--   Equivalently, $c(f^A) = 1 - \min_j f^A_{[n]-j}(j)/f^A_\emptyset(j) \le 1 - 1/\kappa^2(A)$. The result ties a combinatorial parameter of the column-subset selection objective to the conditioning of the matrix, which is what lets the paper's curvature-dependent guarantees for supermodular minimization be quoted for column-subset selection.
--
--   **Formalization Note** "Non-singular" is read as linearly independent columns, the case in which §8 defines $\kappa(A)$ as a ratio. Curvature is written in the product form $f_{X-j}(j) \le (1-c)\,f_\emptyset(j)$, which is (1.1) multiplied out for a decreasing function. Under independence the supremum and infimum over the unit sphere are finite and positive, so $\kappa(A) \ge 1$ is a genuine real number. For $n = 0$ there is no $j$ and the statement is empty, as on the page.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 11, Lemma 8.2 (proof pp. 11–12), with (1.1) p. 3

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace CurvatureSubmod.CSSP

/-- Lemma 8.2, p. 11: for `A` with independent columns, `f^A` has total curvature at most
`1 − 1/κ²(A)`, i.e. `f^A_{[n]−j}(j) ≤ (1/κ²(A)) f^A_∅(j)` for every `j` (product form of (1.1)). -/
theorem lemma_8_2 {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))
    (hc : LinearIndependent ℝ c) :
    CurvatureSubmod.LocalSearch.CurvAtMostDec (fA c) (1 - 1 / condNum c ^ 2) := by sorry

end CurvatureSubmod.CSSP
