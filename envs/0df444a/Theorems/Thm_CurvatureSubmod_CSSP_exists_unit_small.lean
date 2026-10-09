-- Prove2me | Theorems.Thm_CurvatureSubmod_CSSP_exists_unit_small
-- name    : CurvatureSubmod.CSSP.exists_unit_small
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:12.713071+00:00
-- url     : https://prove2.me/theorems/2d7c9f78-50df-42c5-9b26-1d87d38332ae
-- title:
--   Proof of Lemma 8.2, p. 12 — some unit x′ has ‖Ax′‖ ≤ √|f^A_{[n]−i}(i)|
-- statement:
--   Let $A$ be a real $m \times n$ matrix with columns $c_1, \dots, c_n$, and let $f^A$ be the column-subset selection objective. For every $i \in [n]$ there is a unit vector $x' \in \mathbb{R}^n$, $\|x'\| = 1$, with
--   $$\|Ax'\| \le \sqrt{\left|f^A_{[n]-i}(i)\right|} .$$
--
--   A small marginal gain at $[n] - i$ therefore forces $\inf_{\|x\|=1}\|Ax\|$ to be small. This is the other estimate behind Lemma 8.2.
--
--   **Formalization Note** No independence of the columns is assumed; the paper's argument does not use it.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 12, proof of Lemma 8.2, construction of x′

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace CurvatureSubmod.CSSP

/-- Proof of Lemma 8.2, p. 12: some unit vector `x' ∈ ℝⁿ` has `‖Ax'‖ ≤ √|f^A_{[n]−i}(i)|`. -/
theorem exists_unit_small {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
      ‖applyA c x‖ ≤ Real.sqrt |marg (fA c) (Finset.univ.erase i) i| := by sorry

end CurvatureSubmod.CSSP
