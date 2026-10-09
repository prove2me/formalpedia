-- Prove2me | Theorems.Thm_DynTypeMatching_Priority_lemma_A_2_i
-- name    : DynTypeMatching.Priority.lemma_A_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:59:35.150234+00:00
-- url     : https://prove2.me/theorems/884c81dd-e78d-45b0-8bec-7d29dc0926ac
-- title:
--   Lemma A.2(i), Online Appendix A, p. 3 — transferring matching quantity from (i′, j) to a dominant (i, j) weakly improves H_t
-- statement:
--   Consider a well-posed dynamic type matching model, a period $1\le t\le T$, a state $(\mathbf x,\mathbf y)$ and a feasible decision $\mathbf Q$. Suppose $(i,j)\succ_{\mathcal M}(i',j)$, and let $\varepsilon\ge0$ be such that $\mathbf Q+\varepsilon\mathbf e^{m\times n}_{ij}-\varepsilon\mathbf e^{m\times n}_{i'j}$ is also feasible in state $(\mathbf x,\mathbf y)$. Then
--   $$H_t\big(\mathbf Q+\varepsilon\mathbf e^{m\times n}_{ij}-\varepsilon\mathbf e^{m\times n}_{i'j},\mathbf x,\mathbf y\big)\ \ge\ H_t(\mathbf Q,\mathbf x,\mathbf y).$$
--
--   In words: moving $\varepsilon$ units of matching from the dominated pair $(i',j)$ to the dominant pair $(i,j)$ never lowers the total expected reward. This is the exchange step behind the priority theorems.
--
--   **Formalization Note** The page assumes $\mathbf Q$ is a decision; feasibility of $\mathbf Q$ itself is stated explicitly (otherwise $H_t(\mathbf Q,\cdot)$ would evaluate $V_{t+1}$ outside the nonnegative orthant, where it is a junk value), as is $\varepsilon\ge0$ (a transfer). The relation $\succ_{\mathcal M}$ uses the strict and distinct-neighbour form of Definition 1.
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, Online Appendix A, p. 3, Lemma A.2(i)

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model
import Definitions.Def_DynTypeMatching_Priority_Relations

namespace DynTypeMatching.Priority
theorem lemma_A_2_i {m n : ℕ} (M : Model m n) (hM : M.WellPosed) (i i' : Fin m) (j : Fin n)
    (hdom : DomCol M i i' j) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (Q : Fin m → Fin n → ℝ) (hQ : Feasible x y Q)
    (ε : ℝ) (hε : 0 ≤ ε) (hQ' : Feasible x y (Q + ε • unitMat i j - ε • unitMat i' j)) :
    H M t Q x y ≤ H M t (Q + ε • unitMat i j - ε • unitMat i' j) x y := by sorry
end DynTypeMatching.Priority
