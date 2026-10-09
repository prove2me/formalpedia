-- Prove2me | Theorems.Thm_CurvatureSubmod_CSSP_abs_marg_empty
-- name    : CurvatureSubmod.CSSP.abs_marg_empty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:51.428962+00:00
-- url     : https://prove2.me/theorems/b3fde21c-9736-42ef-b94e-520c4dcb1ddf
-- title:
--   Proof of Lemma 8.2, p. 11 — |f^A_∅(i)| = Σ_j ‖proj_{i}(c_j)‖²
-- statement:
--   Let $A$ have columns $c_1, \dots, c_n \in \mathbb{R}^m$ and let $f^A$ be the column-subset selection objective. For every $i \in [n]$, the marginal value of $i$ at the empty set satisfies
--   $$\left|f^A_\emptyset(i)\right| = \sum_{j=1}^n \|\mathrm{proj}_{\{i\}}(c_j)\|^2 ,$$
--   where $\mathrm{proj}_{\{i\}}$ is the orthogonal projection onto the line spanned by $c_i$.
--
--   This is the first step of the proof of Lemma 8.2: the gain of the first column $i$ equals the total squared mass of the columns along $c_i$.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 11, proof of Lemma 8.2, first display

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace CurvatureSubmod.CSSP

/-- Proof of Lemma 8.2, p. 11, first display: `|f^A_∅(i)| = Σ_j ‖proj_{i}(c_j)‖²`. -/
theorem abs_marg_empty {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    |marg (fA c) ∅ i| = ∑ j, ‖proj c {i} (c j)‖ ^ 2 := by sorry

end CurvatureSubmod.CSSP
