-- Prove2me | Theorems.Thm_BimatrixStableSet_theorem_3
-- name    : BimatrixStableSet.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:00.784903+00:00
-- url     : https://prove2.me/theorems/9f743083-59a6-4c26-ab9d-4edb2ae0e594
-- title:
--   Theorem 3 (stable-set bound) — at most $2|S_1|$ equilibria (corrected: $m\ge1$)
-- statement:
--   Let $(A,B)$ be a non-degenerate $m\times n$ game with $m\ge1$ and best-response polytopes $P$ and $Q$. Let $G$ be the graph of $P$, and let $S_1$ and $S_2$ be two disjoint stable sets of $G$ of equal size $|S_1|$, with this size maximal among all such pairs. Then the game has at most
--
--   $$
--   2|S_1|
--   $$
--
--   equilibria, counting the artificial equilibrium $(0,0)$.
--
--   This is the main tool of the paper for bounding the number of equilibria.
--
--   Differences from the source:
--   - encoding: the standing assumptions of the section, stated once → explicit hypotheses `HasBestResponsePolytopes A B` and `IsNondegenerate A B`; reason: same instances
--   - encoding: "at most $c$ equilibria" → `Set.encard` $\le c$ in $\mathbb N_\infty$; reason: finiteness is part of the claim, so no count of an infinite set collapses
--   - correction: any game → $m\ge1$; reason: the $0\times0$ game has the equilibrium $(0,0)$, while every stable pair of its one-point graph is empty, so the printed bound $0$ fails (proved in the verification file)
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Theorem 3, p.12

import Mathlib
import Definitions.Def_BimatrixStableSet_BestResponse
import Definitions.Def_BimatrixStableSet_StableSets

namespace BimatrixStableSet

variable {m n : ℕ}

/-- Theorem 3 (Stable-set bound), p.12 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): let `G`
be the graph of `P` and `S₁`, `S₂` two disjoint stable sets of `G` of equal size `|S₁|`, and let this
size be maximal among all such pairs. Then the game has at most `2|S₁|` equilibria.

**Formalization Note.** The standing assumptions of §5 are hypotheses. "Equilibria" are those of
Definition 1, so `(0, 0)` is counted. The hypothesis `0 < m` corrects the printed statement: the
`0 × 0` game has the one equilibrium `(0, 0)`, but only the empty stable pair. -/
theorem theorem_3 (hm : 0 < m) (A B : Matrix (Fin m) (Fin n) ℝ) (hPQ : HasBestResponsePolytopes A B)
    (hAB : IsNondegenerate A B)
    (S₁ S₂ : Finset ((bestResponseP B).vertices (bestResponseP B).carrier))
    (hS : IsStablePair ((bestResponseP B).graph (bestResponseP B).carrier) S₁ S₂)
    (hmax : ∀ T₁ T₂ : Finset ((bestResponseP B).vertices (bestResponseP B).carrier),
      IsStablePair ((bestResponseP B).graph (bestResponseP B).carrier) T₁ T₂ →
        T₁.card ≤ S₁.card) :
    (equilibria A B).encard ≤ 2 * S₁.card := by sorry

end BimatrixStableSet
