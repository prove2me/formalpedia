-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_lemma_3_4_lower
-- name    : CorrKClust.BalancedPivot.lemma_3_4_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:27.119297+00:00
-- url     : https://prove2.me/theorems/856abf40-d594-4dde-a2b0-fc65325e95ca
-- title:
--   Lemma 3.4 (lower bound) — clique tail mass times water level lower-bounds the optimum
-- statement:
--   Let $G$ be a disjoint union of cliques and let $k\ge1$. For its multiset of positive clique sizes $w$, let $s(w,k)$ and $a(w,k)$ be the quantities of Definitions 3.2–3.3. Then
--   $$\operatorname{OPT}_k(G)\ge\tfrac12 s(w,k)a(w,k).$$
--   This item is the lower-bound clause of Lemma 3.4, used by Lemma 7.4 and equation (29). The algorithmic clauses concerning a polynomial-time greedy approximation and a PTAS are outside the selected clause and are not claimed by this item.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: at most k possibly empty clusters → k > 0 and assignments V → Fin k; reason: positive k is required for an assignment on nonempty inputs and all unused labels remain legal
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 3.4, first sentence only, p. 13, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Lower-bound clause of Lemma 3.4, p. 13; algorithmic clauses are outside this item. -/
theorem lemma_3_4_lower {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k : ℕ} (hk : 0 < k)
    (Q : V → V) (hQ : IsCliquePartition G Q) :
    (cliqueS (blockSizes Q) k : ℝ) * cliqueA (blockSizes Q) k / 2 ≤ (optK G k : ℝ) := by sorry

end CorrKClust.BalancedPivot
