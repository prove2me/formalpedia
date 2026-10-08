-- Prove2me | Theorems.Thm_ConstrNestedLogit_Space_space_guarantee
-- name    : ConstrNestedLogit.Space.space_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:44.488714+00:00
-- url     : https://prove2.me/theorems/75e5cd60-e4ce-4ed7-8ea3-74cd61d9f53e
-- title:
--   One rounded family with both space guarantees
-- statement:
--   For each nest with positive product preference and space weights, and individually feasible products, one collection $\mathcal A_i$ of rounded LP assortments and singletons works for every $u\ge0$. It has at most $(n+1)^2$ feasible members and always includes a two-approximate solution of problem (7). For every $\epsilon\in[0,1)$ satisfying $w_{ij}\le\epsilon c_i$ for all products, the **same** collection also includes a $1/(1-\epsilon)$-approximate solution at every $u\ge0$:
--
--   $$\forall u\ge0,\ \exists S_2,S_\epsilon\in\mathcal A_i:\quad
--   \operatorname{val}_u(T)\le2\operatorname{val}_u(S_2),\quad
--   \operatorname{val}_u(T)\le\frac{1}{1-\epsilon}\operatorname{val}_u(S_\epsilon)
--   \quad\text{for all }T\in C_i.$$
--
--   Here $\operatorname{val}_u(S)=V_i(S)(R_i(S)-u)$. The two guarantees imply the factor $\min\{2,1/(1-\epsilon)\}$ claimed in §5.2, while keeping the candidate family fixed before $u$ and $\epsilon$.
--
--   **Formalization Note** Products form a nonempty finite set, and the within-nest no-purchase weight is zero. Positive preference and space weights are explicit.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 22, concluding paragraph of §5.2

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

namespace ConstrNestedLogit.Space

/-- The one quadratic-size family from §5.1 has both guarantees of §5.2. -/
theorem space_guarantee {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hn : 0 < n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (hw : ∀ j, 0 < w i j) (hwc : ∀ j, w i j ≤ c i) :
    ∃ A : Finset (Finset (Fin n)),
      isRoundedCandidateFamily I w c i A ∧
      (∀ S ∈ A, spaceFeasible w c i S) ∧
      A.card ≤ (n + 1) ^ 2 ∧
      (∀ u : ℝ, 0 ≤ u → ∃ S ∈ A, isApproximateAt I w c i u 2 S) ∧
      (∀ ε : ℝ, 0 ≤ ε → ε < 1 → (∀ j, w i j ≤ ε * c i) →
        ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A,
          isApproximateAt I w c i u (1 / (1 - ε)) S) := by sorry

end ConstrNestedLogit.Space
