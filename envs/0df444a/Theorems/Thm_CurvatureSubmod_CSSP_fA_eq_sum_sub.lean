-- Prove2me | Theorems.Thm_CurvatureSubmod_CSSP_fA_eq_sum_sub
-- name    : CurvatureSubmod.CSSP.fA_eq_sum_sub
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:43.71899+00:00
-- url     : https://prove2.me/theorems/1821c282-a610-4948-b337-b156fa4bf464
-- title:
--   §8, p. 11 — f^A(S) = Σ_i (‖c_i‖² − ‖proj_S(c_i)‖²)
-- statement:
--   Let $c_1, \dots, c_n \in \mathbb{R}^m$ be the columns of a matrix $A$, let $\mathrm{proj}_S$ denote the orthogonal projection onto $\mathrm{span}\{c_i : i \in S\}$, and let $f^A(S) = \sum_{i=1}^n \|c_i - \mathrm{proj}_S(c_i)\|^2$. Then for every $S \subseteq [n]$,
--   $$f^A(S) = \sum_{i=1}^n \left(\|c_i\|^2 - \|\mathrm{proj}_S(c_i)\|^2\right).$$
--
--   This rewrites the residual form of the column-subset selection objective as total squared column norm minus the captured squared norm, which is how the paper passes from $f^A$ to the projection functions of Lemma 8.1.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 11, §8, display defining f^A

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace CurvatureSubmod.CSSP

/-- §8, p. 11, second line of the display defining `f^A`:
`f^A(S) = Σ_i (‖c_i‖² − ‖proj_S(c_i)‖²)`. -/
theorem fA_eq_sum_sub {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    fA c S = ∑ i, (‖c i‖ ^ 2 - ‖proj c S (c i)‖ ^ 2) := by sorry

end CurvatureSubmod.CSSP
