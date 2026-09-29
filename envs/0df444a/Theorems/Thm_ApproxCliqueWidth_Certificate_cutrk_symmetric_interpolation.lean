-- Prove2me | Theorems.Thm_ApproxCliqueWidth_Certificate_cutrk_symmetric_interpolation
-- name    : ApproxCliqueWidth.Certificate.cutrk_symmetric_interpolation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:34:32.744124+00:00
-- url     : https://prove2.me/theorems/18fa59df-1f28-4522-88e5-0b57b050a3ab
-- title:
--   Section 6 claim — $\mathrm{cutrk}_G$ is symmetric submodular and $\mathrm{cutrk}^*_G$ interpolates it
-- statement:
--   Let $G$ be a finite simple graph with vertex set $V$. Then
--
--   1. $\mathrm{cutrk}_G$ is symmetric: $\mathrm{cutrk}_G(X) = \mathrm{cutrk}_G(V \setminus X)$ for all $X \subseteq V$;
--   2. $\mathrm{cutrk}_G$ is submodular;
--   3. $\mathrm{cutrk}_G(\emptyset) \le \mathrm{cutrk}_G(X)$ for all $X \subseteq V$;
--   4. $\mathrm{cutrk}^*_G$ is an interpolation of $\mathrm{cutrk}_G$.
--
--   These facts, announced after Definition 6.1, place the cut-rank function within the hypotheses of Theorems 5.1 and 5.2.
--
--   **Formalization Note** Item 3 is the standing assumption of Definition 4.1 on the function being interpolated; it is included so that the conclusion "$\mathrm{cutrk}^*_G$ is an interpolation of $\mathrm{cutrk}_G$" carries its full meaning in the paper's sense.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 522, Section 6, sentence after Definition 6.1

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Section 6, p. 522, the claim after Definition 6.1: `cutrk_G` is symmetric and
submodular, `∅` minimizes it (the standing assumption of Definition 4.1), and `cutrk*_G` is an
interpolation of `cutrk_G`. -/
theorem cutrk_symmetric_interpolation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsSymmetric (cutrk G) ∧ IsSubmodular (cutrk G) ∧
      (∀ X : Finset V, cutrk G ∅ ≤ cutrk G X) ∧ IsInterpolation (cutrk G) (cutrkStar G) := by sorry

end ApproxCliqueWidth.Certificate
