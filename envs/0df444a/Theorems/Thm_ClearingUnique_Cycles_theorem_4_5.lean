-- Prove2me | Theorems.Thm_ClearingUnique_Cycles_theorem_4_5
-- name    : ClearingUnique.Cycles.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:04.349007+00:00
-- url     : https://prove2.me/theorems/2856df3d-5572-4723-8573-597a96d3d064
-- title:
--   Theorem 4.5, p. 15 — conditions for a unique clearing payment matrix
-- statement:
--   Let $N=(I,z,L,d)$ be a financial network satisfying the standing assumptions. Let $C$ be its cyclical agents and $O(i)$ the strongly connected component of $i$ in the positive-liability graph. Assume:
--
--   1. every cyclical component with no successors has positive total endowment, $\sum_{j\in O(i)}z_j>0$;
--   2. every cyclical agent with $z_i>0$ has a positive-monotonic division rule;
--   3. every cyclical agent with $z_i=0$ has a strictly monotonic division rule.
--
--   Then there exists exactly one clearing payment matrix:
--
--   $$
--   \exists!\,P\in\mathcal M\;\text{such that }P\text{ satisfies Definition 2.2}.
--   $$
--
--   The conditions apply only to cyclical agents; non-cyclical agents need only satisfy the network's standing assumptions. The result identifies when the general division-rule clearing problem has a single outcome.
--
--   **Formalization Note** Clearing is Definition 2.2, with feasibility, limited liability and creditor priority. The conclusion is existence and uniqueness over all matrices, with those conditions inside the clearing predicate; the empty agent set is permitted, as the paper states only finiteness.
-- source:
--   Csóka & Herings, Uniqueness of Clearing Payment Matrices in Financial Networks, GSBE Research Memorandum RM/21/014 (Maastricht University, 8 Sep 2021; doi:10.26481/umagsb.2021014), p. 15 (PDF 17), Theorem 4.5

import Mathlib
import Definitions.Def_ClearingUnique_Cycles_Model

namespace ClearingUnique.Cycles

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem theorem_4_5 (N : FinNetwork I) (hN : N.Standing)
    (h1 : ∀ i, N.Cyclical i → N.NoSuccessors (N.comp i) →
      0 < ∑ j ∈ N.comp i, N.z j)
    (h2 : ∀ i, N.Cyclical i → 0 < N.z i → PositiveMonotonic N i)
    (h3 : ∀ i, N.Cyclical i → N.z i = 0 → StrictlyMonotonic N i) :
    ∃! P : I → I → ℝ, IsClearing N P := by sorry

end ClearingUnique.Cycles
