-- Prove2me | Theorems.Thm_CurvatureSubmod_CSSP_exists_unit_large
-- name    : CurvatureSubmod.CSSP.exists_unit_large
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:24.028999+00:00
-- url     : https://prove2.me/theorems/726befc8-3ac3-43f1-8c92-6b9f1ee08410
-- title:
--   Proof of Lemma 8.2, p. 12 — some unit x has ‖Ax‖ ≥ √|f^A_∅(i)|
-- statement:
--   Let $A$ be a real $m \times n$ matrix with columns $c_1, \dots, c_n$, and let $f^A$ be the column-subset selection objective. For every $i \in [n]$ there is a unit vector $x \in \mathbb{R}^n$, $\|x\| = 1$, with
--   $$\|Ax\| \ge \sqrt{\left|f^A_\emptyset(i)\right|} .$$
--
--   A large marginal gain at the empty set therefore forces $\sup_{\|x\|=1}\|Ax\|$ to be large. This is one of the two estimates that combine into Lemma 8.2.
--
--   **Formalization Note** The statement is existential. The paper exhibits a specific $x$, with $x_j$ proportional to $\|\mathrm{proj}_{\{i\}}(c_j)\|$, and its displayed computation uses $c_i \cdot c_j = \|c_i\|\,\|\mathrm{proj}_{\{i\}}(c_j)\|$, which fails when $c_i \cdot c_j < 0$. The existential claim is true for every $A$ (choose $x_j$ with the sign of $c_i \cdot c_j$). The index $i \in [n]$ forces $n \ge 1$, so unit vectors exist.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), pp. 11–12, proof of Lemma 8.2, Cauchy–Schwarz step

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace CurvatureSubmod.CSSP

/-- Proof of Lemma 8.2, pp. 11–12: some unit vector `x ∈ ℝⁿ` has `‖Ax‖ ≥ √|f^A_∅(i)|`. -/
theorem exists_unit_large {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
      Real.sqrt |marg (fA c) ∅ i| ≤ ‖applyA c x‖ := by sorry

end CurvatureSubmod.CSSP
