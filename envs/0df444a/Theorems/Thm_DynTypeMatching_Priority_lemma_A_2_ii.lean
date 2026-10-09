-- Prove2me | Theorems.Thm_DynTypeMatching_Priority_lemma_A_2_ii
-- name    : DynTypeMatching.Priority.lemma_A_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:59:25.653542+00:00
-- url     : https://prove2.me/theorems/9f8369d8-6cc6-4cfe-b3c0-d95158480504
-- title:
--   Lemma A.2(ii), Online Appendix A, p. 3 — transferring matching quantity from (i, j′) to a dominant (i, j) weakly improves H_t
-- statement:
--   Consider a well-posed dynamic type matching model, a period $1\le t\le T$, a state $(\mathbf x,\mathbf y)$ and a feasible decision $\mathbf Q$. Suppose $(i,j)\succ_{\mathcal M}(i,j')$, and let $\varepsilon\ge0$ be such that $\mathbf Q+\varepsilon\mathbf e^{m\times n}_{ij}-\varepsilon\mathbf e^{m\times n}_{ij'}$ is also feasible in state $(\mathbf x,\mathbf y)$. Then
--   $$H_t\big(\mathbf Q+\varepsilon\mathbf e^{m\times n}_{ij}-\varepsilon\mathbf e^{m\times n}_{ij'},\mathbf x,\mathbf y\big)\ \ge\ H_t(\mathbf Q,\mathbf x,\mathbf y).$$
--
--   This is the row (supply-side) version of Lemma A.2(i).
--
--   **Formalization Note** As in part (i), feasibility of $\mathbf Q$ and of the transferred decision, and $\varepsilon\ge0$, are explicit hypotheses (the page states the feasibility condition only in part (i) and says part (ii) is similar).
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, Online Appendix A, p. 3, Lemma A.2(ii)

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model
import Definitions.Def_DynTypeMatching_Priority_Relations

namespace DynTypeMatching.Priority
theorem lemma_A_2_ii {m n : ℕ} (M : Model m n) (hM : M.WellPosed) (i : Fin m) (j j' : Fin n)
    (hdom : DomRow M i j j') (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (Q : Fin m → Fin n → ℝ) (hQ : Feasible x y Q)
    (ε : ℝ) (hε : 0 ≤ ε) (hQ' : Feasible x y (Q + ε • unitMat i j - ε • unitMat i j')) :
    H M t Q x y ≤ H M t (Q + ε • unitMat i j - ε • unitMat i j') x y := by sorry
end DynTypeMatching.Priority
