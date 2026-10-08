-- Prove2me | Theorems.Thm_ConstrNestedLogit_Card_knapsack_optimal_order_sign
-- name    : ConstrNestedLogit.Card.knapsack_optimal_order_sign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:43.899787+00:00
-- url     : https://prove2.me/theorems/5822b56e-6990-41b3-8196-88e3735b9cee
-- title:
--   pp. 16–17 — the optimal solutions of (9) depend only on the ordering and signs of the utilities
-- statement:
--   Fix a nest $i$, a cardinality limit $c_i \in \mathbb{N}$, and write $f_{ij}(u) = v_{ij}(r_{ij}-u)$ for the utility of product $j$ in problem (9). Let $u, u' \in \mathbb{R}$ be two values at which the utilities have
--
--   1. the same ordering: for all products $j, k$, $f_{ij}(u) \le f_{ik}(u)$ if and only if $f_{ij}(u') \le f_{ik}(u')$;
--   2. the same signs: for every product $j$, $f_{ij}(u)$ and $f_{ij}(u')$ are both positive, both zero, or both negative (the same position relative to the line $f_{i0} = 0$).
--
--   Then for every assortment $S \subseteq N$,
--
--   $$S \text{ is optimal for (9) at } u \iff S \text{ is optimal for (9) at } u'.$$
--
--   Applied to two values in one of the intervals between consecutive intersection points of the lines $\{f_{ij} : j \in N \cup \{0\}\}$, this says that the optimal solution of (9) does not change inside such an interval.
--
--   **Formalization Note** The ordering is compared as a weak order, so ties are allowed, and the conclusion is about the whole set of optimal solutions, not about one selected solution. The signs are compared with Mathlib's `SignType.sign`.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 16–17, discussion of problem (9) and Figure 1

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Card_Knapsack

open NestedLogitVariants.LP

namespace ConstrNestedLogit.Card

/-- The optimal solutions of the knapsack problem (9) depend only on the ordering and signs of
the utilities (pp. 16–17): if at `u` and `u'` the utilities `{f_ij : j ∈ N}` are ordered the
same way (as a weak order, ties included) and have the same signs (comparison with
`f_i0 = 0`), then `S` is optimal for (9) at `u` if and only if it is optimal at `u'`. -/
theorem knapsack_optimal_order_sign {ι : Type*} {n : ℕ} (I : Instance ι n) (c : ι → ℕ) (i : ι)
    (u u' : ℝ)
    (horder : ∀ j k : Fin n, utility I i j u ≤ utility I i k u ↔ utility I i j u' ≤ utility I i k u')
    (hsign : ∀ j : Fin n, SignType.sign (utility I i j u) = SignType.sign (utility I i j u'))
    (S : Finset (Fin n)) :
    IsKnapsackOptimal I c i u S ↔ IsKnapsackOptimal I c i u' S := by sorry

end ConstrNestedLogit.Card
