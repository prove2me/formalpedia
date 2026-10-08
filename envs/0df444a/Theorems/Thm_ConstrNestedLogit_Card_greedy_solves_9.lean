-- Prove2me | Theorems.Thm_ConstrNestedLogit_Card_greedy_solves_9
-- name    : ConstrNestedLogit.Card.greedy_solves_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:09.178244+00:00
-- url     : https://prove2.me/theorems/356adf93-ea0a-460a-92cd-feb05b5c4237
-- title:
--   p. 16 — filling the knapsack with the largest positive utilities solves the unit-weight knapsack problem (9)
-- statement:
--   Fix a nest $i$, a cardinality limit $c_i \in \mathbb{N}$ and $u \in \mathbb{R}$, and write $f_{ij}(u) = v_{ij}(r_{ij}-u)$ for the utility of product $j$. Let $S \subseteq N$ satisfy
--
--   1. $|S| \le c_i$;
--   2. $f_{ij}(u) > 0$ for every $j \in S$;
--   3. $f_{ik}(u) \le f_{ij}(u)$ for every $j \in S$ and every $k \notin S$;
--   4. if $|S| < c_i$, then $f_{ik}(u) \le 0$ for every $k \notin S$.
--
--   These are the sets produced by ordering the products by utility and filling the knapsack from the largest utility as long as the utility is positive. Then $S$ is an optimal solution of problem (9):
--
--   $$\sum_{j \in S} f_{ij}(u) = \max\Bigl\{ \sum_{j\in N} v_{ij}(r_{ij}-u)\,x_{ij} : \sum_{j\in N} x_{ij} \le c_i,\ x_{ij}\in\{0,1\}\ \forall j \in N \Bigr\}.$$
--
--   The result shows that an optimal solution of (9) is read off from the ordering and the signs of the utilities.
--
--   **Formalization Note** The 0/1 vector $x_i$ is the indicator of a `Finset (Fin n)`. Ties among utilities are allowed; any tie-breaking of the greedy order gives an optimal set.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 16, discussion of problem (9)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Card_Knapsack

open NestedLogitVariants.LP

namespace ConstrNestedLogit.Card

/-- Greedy solves the knapsack problem (9) (p. 16): a set `S` with `|S| ≤ c_i` whose products all
have positive utility `f_ij(u) > 0`, such that no product outside `S` has larger utility than a
product in `S`, and such that, if `|S| < c_i`, every product outside `S` has utility `≤ 0`,
is an optimal solution of (9) at `u`. -/
theorem greedy_solves_9 {ι : Type*} {n : ℕ} (I : Instance ι n) (c : ι → ℕ) (i : ι) (u : ℝ)
    (S : Finset (Fin n)) (hcard : S.card ≤ c i)
    (hpos : ∀ j ∈ S, 0 < utility I i j u)
    (horder : ∀ j ∈ S, ∀ k ∉ S, utility I i k u ≤ utility I i j u)
    (hrest : S.card < c i → ∀ k ∉ S, utility I i k u ≤ 0) :
    IsKnapsackOptimal I c i u S := by sorry

end ConstrNestedLogit.Card
