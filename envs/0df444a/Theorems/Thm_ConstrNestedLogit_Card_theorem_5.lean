-- Prove2me | Theorems.Thm_ConstrNestedLogit_Card_theorem_5
-- name    : ConstrNestedLogit.Card.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:42.936257+00:00
-- url     : https://prove2.me/theorems/21d8e5f1-b1dd-4667-8130-1ef4efeef48b
-- title:
--   Theorem 5, p. 17 — under cardinality constraints, at most $(n+1)^2$ candidate assortments include an optimal solution of (7) for every $u \ge 0$
-- statement:
--   Let $i$ be a nest of a nested logit instance with $n$ products, positive preference weights $v_{ij}$ and no within-nest no-purchase weight, so that $V_i(S) = \sum_{j\in S} v_{ij}$; the revenues $r_{ij}$ are arbitrary reals. Let the feasible assortments of nest $i$ be given by the cardinality constraint
--
--   $$\mathcal C_i = \{S \subseteq N : |S| \le c_i\}, \qquad c_i \in \mathbb{N}.$$
--
--   Then there is a collection $\{A_i^t : t \in \mathcal T_i\}$ of assortments in $\mathcal C_i$, fixed independently of $u$, with $|\mathcal T_i| \le (n+1)^2$, such that for every $u \ge 0$ some member $A_i^t$ is an optimal solution of problem (7):
--
--   $$V_i(A_i^t)\,\bigl(R_i(A_i^t) - u\bigr) = \max_{S \in \mathcal C_i} V_i(S)\,\bigl(R_i(S) - u\bigr).$$
--
--   Combined with the paper's Theorems 2 and 4, this means that the constrained assortment problem (1) under cardinality constraints is solved exactly by a linear program with $1+m$ variables and $O(mn^2)$ constraints.
--
--   **Formalization Note** The paper's $|\mathcal T_i| = O(n^2)$ is pinned to the explicit bound $(n+1)^2$; the paper's counting gives at most $n(n+1)/2 + 1$ intervals of $[0,\infty)$. The collection is a `Finset (Finset (Fin n))` quantified before $u$; its members are required to lie in $\mathcal C_i$, and the optimal member beats every assortment of $\mathcal C_i$, not only the other members. Positivity of the $v_{ij}$ and `vnp i = 0` are the model's conventions, stated as hypotheses. Problem (7) contains no dissimilarity parameter, so $\gamma_i$ and $v_0$ do not enter.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 17, Theorem 5

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Card_Knapsack

open NestedLogitVariants.LP

namespace ConstrNestedLogit.Card

/-- Theorem 5 (p. 17): under the cardinality constraint `C_i = {S : |S| ≤ c_i}`, there is a
collection `A` of feasible assortments of nest `i`, with `|A| ≤ (n + 1)²` (the paper's
`|T_i| = O(n²)`) and chosen before `u`, that contains an optimal solution of problem (7) for
every `u ≥ 0`. -/
theorem theorem_5 {ι : Type*} {n : ℕ} (I : Instance ι n) (c : ι → ℕ) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j) :
    ∃ A : Finset (Finset (Fin n)), (∀ S ∈ A, S.card ≤ c i) ∧ A.card ≤ (n + 1) ^ 2 ∧
      ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A, IsOptimal7 I c i u S := by sorry

end ConstrNestedLogit.Card
