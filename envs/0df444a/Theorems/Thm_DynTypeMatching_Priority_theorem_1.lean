-- Prove2me | Theorems.Thm_DynTypeMatching_Priority_theorem_1
-- name    : DynTypeMatching.Priority.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:59:37.522284+00:00
-- url     : https://prove2.me/theorems/b575ef3a-910b-4965-96ff-1e26b0f078bc
-- title:
--   Theorem 1, p. 12 — under the modified Monge condition some optimal matching policy respects ≻Ms
-- statement:
--   Consider a well-posed dynamic type matching model satisfying the modified Monge condition (Definition 2): whenever $(i,j)\succ_{\mathcal M}(i',j)$ and $(i,j)\succ_{\mathcal M}(i,j')$, $r^t_{ij}+r^t_{i'j'}\ge r^t_{ij'}+r^t_{i'j}$ for all $t=1,\dots,T$ (so $\succ_{\mathcal M_s}$ is $\succ_{\mathcal M}$). Then there exists a matching policy $P=\{\mathbf Q^t(\mathbf x,\mathbf y)\}_{t=1,\dots,T}$ that is optimal and respects $\succ_{\mathcal M_s}$: for every period $1\le t\le T$ and every state $\mathbf x\ge0$, $\mathbf y\ge0$, the decision $\mathbf Q=\mathbf Q^t(\mathbf x,\mathbf y)$ is optimal and
--
--   $$\begin{aligned}&(i,j)\succ_{\mathcal M_s}(i',j)\ \Longrightarrow\ q_{i'j}=0\ \text{ or }\ a_i=0,\\ &(i,j)\succ_{\mathcal M_s}(i,j')\ \Longrightarrow\ q_{ij'}=0\ \text{ or }\ b_j=0,\end{aligned}$$
--   with $a_i=x_i-\sum_{j'':(i,j'')\notin\mathcal B_{ij,L}}q_{ij''}$ and $b_j=y_j-\sum_{i'':(i'',j)\notin\mathcal B_{ij,R}}q_{i''j}$.
--
--   In that policy, matching of $(i,j)$ is prioritized over every neighbouring pair it dominates, in every period and state: this is the paper's main structural result, from which greedy matching of perfect pairs and the priority structure of the horizontal and vertical models follow.
--
--   **Formalization Note** A single policy is both optimal and compatible. Definition 1 is used in its strict, distinct-neighbour form; with the printed weak inequality the theorem is false ($m=3$, $n=1$, $T=1$, all rewards $2$, $\mathbf x=(0,1,1)$, $\mathbf y=(1)$: types 2 and 3 dominate each other, and no decision matching one unit satisfies Definition 3). Condition (ii) of Definition 1 is required for $t+1\le T$. Optimality compares $H_t$ over feasible decisions. Well-posedness includes the integrability of arrivals that makes (1) well defined.
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, p. 12, Theorem 1 (Definitions 1–3, p. 11)

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model
import Definitions.Def_DynTypeMatching_Priority_Relations

namespace DynTypeMatching.Priority
theorem theorem_1 {m n : ℕ} (M : Model m n) (hM : M.WellPosed) (hMonge : MongeCondition M) :
    ∃ P : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → (Fin m → Fin n → ℝ),
      IsOptimalPolicy M P ∧
        ∀ t, 1 ≤ t → t ≤ M.T → ∀ (x : Fin m → ℝ) (y : Fin n → ℝ), 0 ≤ x → 0 ≤ y →
          Respects M x y (P t x y) := by sorry
end DynTypeMatching.Priority
