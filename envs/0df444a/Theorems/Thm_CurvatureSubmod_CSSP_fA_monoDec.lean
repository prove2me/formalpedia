-- Prove2me | Theorems.Thm_CurvatureSubmod_CSSP_fA_monoDec
-- name    : CurvatureSubmod.CSSP.fA_monoDec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:34.92898+00:00
-- url     : https://prove2.me/theorems/24eb082b-16b0-424d-ae03-1c4dbfa67865
-- title:
--   §8, p. 11 (monotone part of the claim before Lemma 8.1) — f^A is monotone decreasing
-- statement:
--   Let $A$ be a real $m \times n$ matrix with columns $c_1, \dots, c_n$ and let $f^A(S) = \sum_{i=1}^n \|c_i - \mathrm{proj}_S(c_i)\|^2$ be the column-subset selection objective. Then $f^A$ is monotone decreasing:
--   $$f^A(S + i) - f^A(S) \le 0 \qquad \text{for all } S \subseteq [n],\ i \in [n].$$
--
--   Adding a column to the selected set can only shrink the residual. Monotonicity is what makes the total curvature of $f^A$ (Lemma 8.2) meaningful.
--
--   **Formalization Note** The paper's sentence also claims that $f^A$ is supermodular. That half is false and is not stated: with columns $e_1, e_1 + e_2, 2e_2$ in $\mathbb{R}^2$, $f^A(\{1\}) + f^A(\{2\}) = 5 + \tfrac52 > 0 + 7 = f^A(\{1,2\}) + f^A(\emptyset)$, and perturbing the last column to $(0, 2, 0.1)$ in $\mathbb{R}^3$ gives a counterexample with independent columns.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 11, §8, sentence before Lemma 8.1 (monotonicity part)

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace CurvatureSubmod.CSSP

/-- §8, p. 11, sentence before Lemma 8.1, its monotonicity half: `f^A` is monotone decreasing.
The printed supermodularity half is false (columns `e₁, e₁ + e₂, 2e₂`) and is not stated. -/
theorem fA_monoDec {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) :
    MonoDec (fA c) := by sorry

end CurvatureSubmod.CSSP
