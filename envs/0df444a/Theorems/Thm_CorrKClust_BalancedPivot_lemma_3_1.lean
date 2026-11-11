-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_lemma_3_1
-- name    : CorrKClust.BalancedPivot.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:53.670257+00:00
-- url     : https://prove2.me/theorems/6b4195b1-20a8-4ff8-afd6-35b39b205261
-- title:
--   Lemma 3.1 — an optimal k-clustering keeps disjoint cliques intact
-- statement:
--   Let $G$ be a disjoint union of cliques given by the nonempty blocks of a partition $Q$, and let $k\ge1$. There is a clustering $f$ attaining the unrestricted k-clustering minimum and preserving every clique:
--   $$\operatorname{Cost}_G(f)=\operatorname{OPT}_k(G),\qquad Q(u)=Q(v)\Longrightarrow f(u)=f(v).$$
--   This supplies an optimal solution with the whole-clique property needed by the clique lower bound. It asserts existence of such an optimum rather than imposing clique preservation in the definition of the optimum.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: at most k possibly empty clusters → k > 0 and assignments V → Fin k; reason: positive k is required for an assignment on nonempty inputs and all unused labels remain legal
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 3.1, p. 12, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Lemma 3.1, p. 12: some optimal assignment keeps each component clique intact. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k : ℕ} (hk : 0 < k)
    (Q : V → V) (hQ : IsCliquePartition G Q) :
    ∃ f : V → Fin k, cost G f = optK G k ∧
      ∀ u v, Q u = Q v → f u = f v := by sorry

end CorrKClust.BalancedPivot
