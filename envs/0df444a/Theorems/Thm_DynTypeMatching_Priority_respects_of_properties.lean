-- Prove2me | Theorems.Thm_DynTypeMatching_Priority_respects_of_properties
-- name    : DynTypeMatching.Priority.respects_of_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:59:20.526698+00:00
-- url     : https://prove2.me/theorems/b975dcfd-ad09-45b3-9fbb-665ec4dfc0e5
-- title:
--   Proof of Theorem 1, Online Appendix A, p. 5 — properties (i)–(iii) of a decision imply compatibility (Definition 3)
-- statement:
--   Fix a dynamic type matching model, a state $(\mathbf x,\mathbf y)$ and a decision $\mathbf Q$ with post-matching levels $\mathbf u,\mathbf v$. Suppose:
--
--   1. for every $(i,j)\succ_{\mathcal M}(i',j)$: $q_{i'j}=0$ or $u_i=0$;
--   2. for every $(i,j)\succ_{\mathcal M}(i,j')$: $q_{ij'}=0$ or $v_j=0$;
--   3. for every $(i,j)\succ_{\mathcal M}(i,j')$ and $(i,j)\succ_{\mathcal M}(i',j)$: $q_{i'j}=0$ or $q_{ij'}=0$.
--
--   Then $\mathbf Q$ respects the relation in the sense of Definition 3:
--   $$\begin{aligned}&(i,j)\succ_{\mathcal M}(i',j)\ \Longrightarrow\ q_{i'j}=0\ \text{ or }\ a_i=0,\\ &(i,j)\succ_{\mathcal M}(i,j')\ \Longrightarrow\ q_{ij'}=0\ \text{ or }\ b_j=0.\end{aligned}$$
--
--   This is the combinatorial step that turns weak compatibility plus the Monge-exchange property into full compatibility in the proof of Theorem 1.
--
--   **Formalization Note** The page concludes "either $q^t_{i'j}=0$ and $a^t_i=0$"; the intended (and proved) statement is the disjunction of Definition 3. No feasibility or Monge hypothesis is needed for this step.
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, Online Appendix A, p. 5, proof of Theorem 1, properties (i)–(iii)

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model
import Definitions.Def_DynTypeMatching_Priority_Relations

namespace DynTypeMatching.Priority
theorem respects_of_properties {m n : ℕ} (M : Model m n) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (Q : Fin m → Fin n → ℝ)
    (h1 : ∀ (i i' : Fin m) (j : Fin n), DomCol M i i' j → Q i' j = 0 ∨ postD x Q i = 0)
    (h2 : ∀ (i : Fin m) (j j' : Fin n), DomRow M i j j' → Q i j' = 0 ∨ postS y Q j = 0)
    (h3 : ∀ (i i' : Fin m) (j j' : Fin n), DomCol M i i' j → DomRow M i j j' →
      Q i' j = 0 ∨ Q i j' = 0) :
    Respects M x y Q := by sorry
end DynTypeMatching.Priority
