-- Prove2me | Theorems.Thm_CombOpt_MatroidPolytope_greedy_optimal_iff_isMatroid
-- name    : CombOpt.MatroidPolytope.greedy_optimal_iff_isMatroid
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:20.546164+00:00
-- url     : https://prove2.me/theorems/1738de6d-35c4-49ef-898a-cbe510245a37
-- title:
--   Theorem 8.3 — the Greedy Algorithm is optimal for every weighting iff the independence system is a matroid
-- statement:
--   Let $(S,\mathcal I)$ be an independence system on a finite set $S$, i.e. $\emptyset\in\mathcal I$ and $\mathcal I$ is closed under taking subsets. Then:
--
--   1. $(S,\mathcal I)$ is a matroid if and only if, for every $c\in\mathbb R^S$, **every** set the Greedy Algorithm can return is a maximum-weight independent set;
--   2. $(S,\mathcal I)$ is a matroid if and only if, for every $c\in\mathbb R^S$, **some** run of the Greedy Algorithm returns a maximum-weight independent set.
--
--   So matroids are exactly the independence systems on which greedy optimization works for all weightings, however ties are broken.
--
--   Differences from the source:
--   - reading: "the Greedy Algorithm finds an optimal independent set for every c" → stated twice, once for every run and once for some run of the algorithm; reason: ties are broken arbitrarily (p. 274), so "finds" can be read either way, and any fixed tie-breaking rule lies between the two readings; stating both covers every reading
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 8.3, p. 277 (PDF p. 284)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_IsMaxWeightIndep
import Definitions.Def_CombOpt_MatroidPolytope_IsGreedyOutput

namespace CombOpt.MatroidPolytope

/-- **Theorem 8.3: the Greedy Algorithm characterizes matroids.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 8.3, p. 277 (PDF p. 284): "Let (S, I) be an independence system. Then the Greedy
Algorithm finds an optimal independent set for every c ∈ R^S if and only if (S, I) is a matroid."
An *independence system* is a pair satisfying (M0) and (M1) (p. 277).

For an independence system `I` on a finite ground set, both readings of "the Greedy Algorithm
finds an optimal independent set" are stated:
1. `I` is a matroid iff, for every `c`, **every** set the algorithm can return is a
   maximum-weight independent set;
2. `I` is a matroid iff, for every `c`, **some** run of the algorithm returns a maximum-weight
   independent set.

**Formalization Note.** Ties in the algorithm are broken arbitrarily (p. 274), so "finds" can be
read for every run or for some run; the conjunction covers both readings (and every fixed
tie-breaking rule, which lies between them). -/
theorem greedy_optimal_iff_isMatroid {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α → Prop) (hI : SubsamplingSM.Offline.IsIndepSystem I) :
    (IsMatroid I ↔
        ∀ (c : α → ℝ) (J : Finset α), IsGreedyOutput I c J → IsMaxWeightIndep I c J) ∧
      (IsMatroid I ↔
        ∀ c : α → ℝ, ∃ J : Finset α, IsGreedyOutput I c J ∧ IsMaxWeightIndep I c J) := by sorry

end CombOpt.MatroidPolytope
