-- Prove2me | Theorems.Thm_CombOpt_MatroidPolytope_greedy_maxWeight
-- name    : CombOpt.MatroidPolytope.greedy_maxWeight
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:49.539979+00:00
-- url     : https://prove2.me/theorems/24e09a53-902a-4dab-a241-e7b674cb18a3
-- title:
--   Theorem 8.2 — the Greedy Algorithm finds a maximum-weight independent set of a matroid
-- statement:
--   Let $M=(S,\mathcal I)$ be a matroid on a finite set $S$ and let $c\in\mathbb R^S$ be arbitrary weights. Then every set $J$ that the Greedy Algorithm can return (whatever choice it makes among elements of equal weight) is a maximum-weight independent set:
--   $$J\in\mathcal I\quad\text{and}\quad c(J)\ge c(J')\ \text{ for all } J'\in\mathcal I.$$
--
--   This is the result of Rado (1957), rediscovered by Edmonds (1970), that gives the Greedy Algorithm its name.
--
--   Differences from the source:
--   - reading: "the greedy algorithm finds a maximum-weight independent set" → every set returned by some run of the nondeterministic algorithm is maximum-weight; reason: the book breaks ties arbitrarily (p. 274), and its proof of Theorem 8.3 treats every run; "every run" is the stronger reading
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 8.2, p. 276 (PDF p. 283)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_IsMaxWeightIndep
import Definitions.Def_CombOpt_MatroidPolytope_IsGreedyOutput

namespace CombOpt.MatroidPolytope

/-- **Theorem 8.2: the Greedy Algorithm is optimal on matroids (Rado 1957, Edmonds 1970).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 8.2, p. 276 (PDF p. 283): "For any matroid M = (S, I) and any c ∈ R^S, the greedy
algorithm finds a maximum-weight independent set."

For a matroid `I` on a finite ground set and any weights `c`, every set the Greedy Algorithm can
return (whatever the tie-breaking) is a maximum-weight independent set.

**Formalization Note.** "Finds" is read as: every run of the algorithm ends at a maximum-weight
independent set (ties are broken arbitrarily, p. 274). -/
theorem greedy_maxWeight {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α → Prop)
    (hI : IsMatroid I) (c : α → ℝ) (J : Finset α) (hJ : IsGreedyOutput I c J) :
    IsMaxWeightIndep I c J := by sorry

end CombOpt.MatroidPolytope
