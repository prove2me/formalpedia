-- Prove2me | Theorems.Thm_DynTypeMatching_Priority_theorem_2
-- name    : DynTypeMatching.Priority.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:59:20.426677+00:00
-- url     : https://prove2.me/theorems/62be1bdf-d63c-4656-a83c-65236ef61100
-- title:
--   Theorem 2, p. 28 — there exists an optimal matching policy that weakly respects ≻M
-- statement:
--   Consider a well-posed dynamic type matching model (no Monge condition is assumed). Then there is a matching policy $P=\{\mathbf Q^t(\mathbf x,\mathbf y)\}_{t=1,\dots,T}$ that is optimal and weakly respects $\succ_{\mathcal M}$: for every period $1\le t\le T$ and every state $\mathbf x\ge0$, $\mathbf y\ge0$, the decision $\mathbf Q=\mathbf Q^t(\mathbf x,\mathbf y)$ is optimal and
--
--   $$\begin{aligned}&(i,j)\succ_{\mathcal M}(i',j)\ \Longrightarrow\ q_{i'j}=0\ \text{ or }\ u_i=0,\\ &(i,j)\succ_{\mathcal M}(i,j')\ \Longrightarrow\ q_{ij'}=0\ \text{ or }\ v_j=0,\end{aligned}$$
--   where $\mathbf u,\mathbf v$ are the post-matching levels of $\mathbf Q$.
--
--   In words: a dominated pair is matched only once the dominant pair's demand (resp. supply) side is exhausted.
--
--   **Formalization Note** One policy is both optimal and weakly compatible (a single existential). The relation $\succ_{\mathcal M}$ uses the strict, distinct-neighbour form of Definition 1; with the printed weak inequality the theorem is false (counterexample in the definition of the relations).
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, p. 28, Theorem 2 (Definition 4, p. 28); proof in Online Appendix A, p. 4

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model
import Definitions.Def_DynTypeMatching_Priority_Relations

namespace DynTypeMatching.Priority
theorem theorem_2 {m n : ℕ} (M : Model m n) (hM : M.WellPosed) :
    ∃ P : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → (Fin m → Fin n → ℝ),
      IsOptimalPolicy M P ∧
        ∀ t, 1 ≤ t → t ≤ M.T → ∀ (x : Fin m → ℝ) (y : Fin n → ℝ), 0 ≤ x → 0 ≤ y →
          WeaklyRespects M x y (P t x y) := by sorry
end DynTypeMatching.Priority
