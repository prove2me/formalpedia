-- Prove2me | Theorems.Thm_ConstrNestedLogit_Pricing_selection_rule_optimal
-- name    : ConstrNestedLogit.Pricing.selection_rule_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:49.350979+00:00
-- url     : https://prove2.me/theorems/31156e46-80cb-4f08-99ac-7e142e928527
-- title:
--   §6, p. 24 — per-product selection rule: the best positive coefficient in each $N_k$ solves problem (12)
-- statement:
--   Consider nest $i$ of the joint assortment and pricing problem, with $v_{i0}=0$ and positive preference weights $v_{ij}>0$, and fix $u\ge 0$. Write $f_{ij}(u)=v_{ij}(r_{ij}-u)$ for the objective coefficient of virtual product $j$.
--
--   Suppose an assortment $S_i$ is built product by product as follows: for every product $k\in P$,
--
--   1. if $f_{ij}(u)\le 0$ for all $j\in N_k$, then $S_i$ contains no virtual product of $N_k$;
--   2. otherwise $S_i\cap N_k=\{j_k\}$ for some $j_k\in N_k$ with $f_{ij_k}(u)>0$ and $f_{ij_k}(u)\ge f_{ij}(u)$ for all $j\in N_k$.
--
--   Then $S_i$ is an optimal solution of problem (7) at $u$ over $\mathcal C_i$:
--   $$
--   S_i\in\mathcal C_i\quad\text{and}\quad V_i(S_i)\,(R_i(S_i)-u)\ \ge\ V_i(S_i')\,(R_i(S_i')-u)\quad\text{for all } S_i'\in\mathcal C_i .
--   $$
--
--   This is the rule by which the paper solves problem (12), the linear form of problem (7) under the pricing constraints. It shows that the optimal choice within each $N_k$ depends only on the ordering and signs of the coefficients $\{f_{ij}(u):j\in N_k\}$.
--
--   **Formalization Note** The page leaves $v_{ij}>0$ and $v_{i0}=0$ implicit (they make problem (7) equal to problem (12) through (8)); both are stated as hypotheses. When the largest coefficient is exactly $0$ the rule offers nothing, as on the page.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 24, §6, the rule for problem (12)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Pricing_Model

namespace ConstrNestedLogit.Pricing

open NestedLogitVariants.LP

/-- §6, p. 24, the per-product rule for problem (12): for each product `k`, offer one virtual
product of `N_k` with the largest coefficient `f_ij(u)` if that coefficient is positive, and no
virtual product of `N_k` otherwise. The resulting assortment is optimal for problem (7). -/
theorem selection_rule_optimal {ι : Type*} {n p : ℕ} (I : Instance ι n) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (prod : Fin n → Fin p) (u : ℝ) (hu : 0 ≤ u) (S : Finset (Fin n))
    (hS : ∀ k : Fin p,
      ((∀ j, prod j = k → coeff I i u j ≤ 0) ∧ S.filter (fun j => prod j = k) = ∅) ∨
      (∃ j, prod j = k ∧ 0 < coeff I i u j ∧
        (∀ j', prod j' = k → coeff I i u j' ≤ coeff I i u j) ∧
        S.filter (fun j' => prod j' = k) = {j})) :
    IsOptimal7 I prod i u S := by sorry

end ConstrNestedLogit.Pricing
