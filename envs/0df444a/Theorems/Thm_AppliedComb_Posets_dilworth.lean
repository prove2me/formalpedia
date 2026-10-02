-- Prove2me | Theorems.Thm_AppliedComb_Posets_dilworth
-- name    : AppliedComb.Posets.dilworth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:07:36.282392+00:00
-- url     : https://prove2.me/theorems/85fd1f07-da9b-4330-ba55-635192c1bdb7
-- title:
--   Theorem 6.17 — Dilworth's Theorem
-- statement:
--   Let $\mathbf P = (X, P)$ be a finite poset and let $w = \operatorname{width}(\mathbf P)$ be the largest size of an antichain (a set of pairwise incomparable points). Then $X$ can be partitioned into $w$ chains,
--   $$X = C_1 \cup C_2 \cup \cdots \cup C_w, \qquad C_i \text{ a chain}, \ C_i \cap C_j = \emptyset \ (i \ne j),$$
--   and there is no partition of $X$ into fewer than $w$ chains.
--
--   Thus the least number of chains needed to cover a finite poset equals the size of its largest antichain. The theorem is equivalent to König's theorem on bipartite matchings and to Hall's marriage theorem, and it is the capstone of the chapter.
--
--   **Formalization Note.** Stated for a finite type `α` (the book defines width as a maximum, which presumes finiteness). Width is defined from antichains (`AppliedComb.Posets.width`), never as a minimum number of chains, so the statement is not true by definition. The partition is indexed by `Fin (width α)`; the "no fewer" clause quantifies over every `k` and every chain partition indexed by `Fin k`, and concludes `width α ≤ k`. The empty poset ($w = 0$) is included.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 122, Theorem 6.17

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_AppliedComb_Posets_chainPartition

namespace AppliedComb.Posets

/-- Theorem 6.17 (Dilworth's Theorem), Keller & Trotter p. 122: a finite poset of width `w`
has a partition into `w` chains, and every chain partition has at least `w` parts. -/
theorem dilworth (α : Type*) [PartialOrder α] [Fintype α] :
    (∃ C : Fin (width α) → Finset α, IsChainPartition C) ∧
    ∀ (k : ℕ) (C : Fin k → Finset α), IsChainPartition C → width α ≤ k := by sorry

end AppliedComb.Posets
