-- Prove2me | Theorems.Thm_ConstrNestedLogit_Pricing_pricing_candidates
-- name    : ConstrNestedLogit.Pricing.pricing_candidates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:56.42098+00:00
-- url     : https://prove2.me/theorems/98cbbd79-aff1-4117-a525-ab224a0b1f4f
-- title:
--   §6, pp. 24–25 — joint assortment and pricing: $p(b+1)^2+1$ candidates per nest contain an optimal solution of (7) for every $u\ge 0$
-- statement:
--   Consider nest $i$ of the joint assortment and pricing problem: $p$ products, each offered at no more than one of $b$ price levels, encoded as $n=pb$ virtual products with $|N_k|=b$ for every product $k$; arbitrary prices $r_{ij}$, positive preference weights $v_{ij}>0$, and $v_{i0}=0$. Let $\mathcal C_i$ be the feasible set of assortments that offer at most one virtual product of each product.
--
--   Then there is a collection $\{A_i^t:t\in\mathcal T_i\}\subseteq\mathcal C_i$ of feasible assortments, with
--   $$
--   |\mathcal T_i|\ \le\ p\,(b+1)^2+1,
--   $$
--   such that for every $u\ge 0$ some member $A_i^t$ is an optimal solution of problem (7),
--   $$
--   V_i(A_i^t)\,(R_i(A_i^t)-u)\ \ge\ V_i(S_i)\,(R_i(S_i)-u)\qquad\text{for all } S_i\in\mathcal C_i .
--   $$
--   The collection is chosen once, before $u$.
--
--   This is the paper's joint assortment and pricing result with $|\mathcal T_i|=O(pb^2)$. Combined with the paper's Theorems 2 and 4 (with $\alpha=1$), it yields an optimal solution of the joint assortment and pricing problem from a linear program with $1+m$ variables and $O(mpb^2)$ constraints.
--
--   **Formalization Note** The page's $O(pb^2)$ is pinned to $p(b+1)^2+1$: for each product the $b+1$ lines $\{f_{ij}:j\in N_k\cup\{0\}\}$, $f_{ij}(u)=v_{ij}(r_{ij}-u)$, $f_{i0}=0$, meet in at most $b(b+1)/2$ points, and $1+p\,b(b+1)/2\le p(b+1)^2+1$ intervals of $[0,\infty)$ remain. Products are `Fin p`, virtual products `Fin n`, and $N_k$ is the fiber of a map `prod : Fin n → Fin p` of size $b$. The relation between price and weight is arbitrary. The hypotheses $v_{ij}>0$ and $v_{i0}=0$ are stated explicitly.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 24–25, §6, the collection {A_i^t : t ∈ T_i} with |T_i| = O(p b²)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Pricing_Model

namespace ConstrNestedLogit.Pricing

open NestedLogitVariants.LP

/-- §6, pp. 24–25: in the joint assortment and pricing problem with `p` products and `b` price
levels per product, each nest `i` has a collection of at most `p (b + 1)^2 + 1` feasible
assortments that contains an optimal solution of problem (7) for every `u ≥ 0`. -/
theorem pricing_candidates {ι : Type*} {n p b : ℕ} (I : Instance ι n) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (prod : Fin n → Fin p) (hb : IsVirtualProductMap prod b) :
    ∃ A : Finset (Finset (Fin n)),
      (∀ S ∈ A, PricingFeasible prod S) ∧
      A.card ≤ p * (b + 1) ^ 2 + 1 ∧
      ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A, IsOptimal7 I prod i u S := by sorry

end ConstrNestedLogit.Pricing
