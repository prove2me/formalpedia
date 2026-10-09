-- Prove2me | Theorems.Thm_DynTypeMatching_Priority_monge_exchange
-- name    : DynTypeMatching.Priority.monge_exchange
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:59:47.632903+00:00
-- url     : https://prove2.me/theorems/d46e6338-2c47-4340-b7e2-0a651e797d8e
-- title:
--   Proof of Theorem 1, Online Appendix A, p. 4 — a Monge exchange keeps the decision feasible and weakly improves H_t
-- statement:
--   Consider a well-posed dynamic type matching model satisfying the modified Monge condition, a period $1\le t\le T$, a state $(\mathbf x,\mathbf y)$ and a feasible decision $\mathbf Q$. Let $i,i'$ be demand types and $j,j'$ supply types with $(i,j)\succ_{\mathcal M_s}(i',j)$ and $(i,j)\succ_{\mathcal M_s}(i,j')$. Set $\varepsilon=\min\{q_{i'j},q_{ij'}\}$ and put
--   $$\mathbf Q'=\mathbf Q+\varepsilon\mathbf e^{m\times n}_{ij}+\varepsilon\mathbf e^{m\times n}_{i'j'}-\varepsilon\mathbf e^{m\times n}_{i'j}-\varepsilon\mathbf e^{m\times n}_{ij'}.$$
--   Then $\mathbf Q'$ is feasible in state $(\mathbf x,\mathbf y)$ and $H_t(\mathbf Q',\mathbf x,\mathbf y)\ge H_t(\mathbf Q,\mathbf x,\mathbf y)$.
--
--   This is the additional transfer used in the proof of Theorem 1, beyond those of Theorem 2: it moves matching off the two pairs dominated by $(i,j)$ while keeping every post-matching level unchanged.
--
--   **Formalization Note** The page writes $\mathbf Q^k+\varepsilon\mathbf e_{ij}+\varepsilon\mathbf e_{ij}-\varepsilon\mathbf e_{i'j}-\varepsilon\mathbf e_{ij'}$; the second term is $\varepsilon\mathbf e_{i'j'}$ (otherwise row and column sums change). The page writes the two source quantities as $q^{t*}$ while applying the transfer to $\mathbf Q^k$; the Lean statement uses the entries of $\mathbf Q$.
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, Online Appendix A, p. 4, proof of Theorem 1 (the transfer Q^{k+1})

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model
import Definitions.Def_DynTypeMatching_Priority_Relations

namespace DynTypeMatching.Priority
theorem monge_exchange {m n : ℕ} (M : Model m n) (hM : M.WellPosed) (t : ℕ) (ht1 : 1 ≤ t)
    (htT : t ≤ M.T) (x : Fin m → ℝ) (y : Fin n → ℝ) (Q : Fin m → Fin n → ℝ)
    (hQ : Feasible x y Q) (hMonge : MongeCondition M) (i i' : Fin m) (j j' : Fin n)
    (hCol : DomCol M i i' j) (hRow : DomRow M i j j')
    (ε : ℝ) (hε : ε = min (Q i' j) (Q i j')) :
    Feasible x y (Q + ε • unitMat i j + ε • unitMat i' j' - ε • unitMat i' j - ε • unitMat i j') ∧
      H M t Q x y ≤
        H M t (Q + ε • unitMat i j + ε • unitMat i' j' - ε • unitMat i' j - ε • unitMat i j') x y := by sorry
end DynTypeMatching.Priority
