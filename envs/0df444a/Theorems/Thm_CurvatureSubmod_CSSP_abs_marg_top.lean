-- Prove2me | Theorems.Thm_CurvatureSubmod_CSSP_abs_marg_top
-- name    : CurvatureSubmod.CSSP.abs_marg_top
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:49.866769+00:00
-- url     : https://prove2.me/theorems/3de42013-e44b-4b82-a29f-a1b42bde6249
-- title:
--   Proof of Lemma 8.2, p. 12 — |f^A_{[n]−i}(i)| = ‖c_i − proj_{[n]−i}(c_i)‖²
-- statement:
--   Let $A$ have columns $c_1, \dots, c_n \in \mathbb{R}^m$ and let $f^A$ be the column-subset selection objective. For every $i \in [n]$, the marginal value of $i$ at $[n] - i$ satisfies
--   $$\left|f^A_{[n]-i}(i)\right| = \|c_i - \mathrm{proj}_{[n]-i}(c_i)\|^2 ,$$
--   the squared distance from $c_i$ to the span of the other columns.
--
--   This is the second step of the proof of Lemma 8.2: the last column's gain is its distance to the other columns.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 12, proof of Lemma 8.2, display for f^A_{[n]−i}(i)

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace CurvatureSubmod.CSSP

/-- Proof of Lemma 8.2, p. 12: `|f^A_{[n]−i}(i)| = ‖c_i − proj_{[n]−i}(c_i)‖²`. -/
theorem abs_marg_top {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    |marg (fA c) (Finset.univ.erase i) i| =
      ‖c i - proj c (Finset.univ.erase i) (c i)‖ ^ 2 := by sorry

end CurvatureSubmod.CSSP
