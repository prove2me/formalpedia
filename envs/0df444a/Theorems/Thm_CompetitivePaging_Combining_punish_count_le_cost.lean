-- Prove2me | Theorems.Thm_CompetitivePaging_Combining_punish_count_le_cost
-- name    : CompetitivePaging.Combining.punish_count_le_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:23:09.326845+00:00
-- url     : https://prove2.me/theorems/9b077633-729b-43f6-962a-bd73b170a5a7
-- title:
--   Each punishment is paid for by a move of the punished algorithm
-- statement:
--   Let $M$ be a finite vertex set with the uniform metric, and let $A$, $B$ be deterministic on-line algorithms with $k$ servers on $M$, where $A$ never places two servers on the same vertex. Then for every request sequence $\sigma$ the cost of $B$ is at least the number of time steps at which $A$ punishes $B$:
--   $$\mathrm{PUN}(A,B,|\sigma|,\sigma)\le C_B(\sigma).$$
--
--   This is the first half of the accounting in the sufficiency proof of Theorem 6: to make $A$ competitive against $B$ it is enough that $A$ punishes $B$ often.
--
--   **Formalization Note** The paper takes the sets of covered vertices to have cardinality $k$; for $A$ this is the hypothesis that every configuration of $A$ is injective. $B$ is arbitrary.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 9 (PDF p. 10), §6, proof of Theorem 6 (sufficiency)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Combining_punishCount

namespace CompetitivePaging.Combining

/-- Fiat et al. 1991, §6, proof of Theorem 6, p. 9: "Clearly, `C_B(σ)` is at least as great as
the number of time steps at which `A` punishes `B`." Paging setting: uniform metric on `M`;
`A` keeps its servers on distinct vertices (the paper's `S(A, t)` has cardinality `k`). -/
theorem punish_count_le_cost {k : ℕ} {M : Type} [MetricSpace M] [Fintype M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1)
    (A B : KServer.OnlineAlgorithm k M)
    (hA : ∀ l : List M, Function.Injective (A.conf l)) (σ : List M) :
    (punishCount A B σ σ.length : ℝ) ≤ B.cost σ := by sorry

end CompetitivePaging.Combining
