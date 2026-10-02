-- Prove2me | Theorems.Thm_AppliedComb_Posets_dual_dilworth
-- name    : AppliedComb.Posets.dual_dilworth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:06:06.06345+00:00
-- url     : https://prove2.me/theorems/193f7294-2b0d-4af6-baf5-6809f0c9d71a
-- title:
--   Theorem 6.18 — Dual of Dilworth's Theorem (Mirsky)
-- statement:
--   Let $\mathbf P = (X, P)$ be a finite poset and let $h = \operatorname{height}(\mathbf P)$ be the largest size of a chain in $\mathbf P$. Then $X$ can be partitioned into $h$ antichains,
--   $$X = A_1 \cup A_2 \cup \cdots \cup A_h, \qquad A_i \text{ an antichain}, \ A_i \cap A_j = \emptyset \ (i \ne j),$$
--   and there is no partition of $X$ into fewer than $h$ antichains.
--
--   Equivalently, the least number of antichains in a partition of a finite poset equals the size of its largest chain. It is the dual of Dilworth's theorem, with chains and antichains exchanged.
--
--   **Formalization Note.** Stated for a finite type `α` (the book defines height as a maximum, which presumes finiteness). The partition is indexed by `Fin (height α)`; the "no fewer" clause quantifies over every `k` and every antichain partition indexed by `Fin k`, and concludes `height α ≤ k`. The empty poset ($h = 0$) is included.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 122, Theorem 6.18

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_AppliedComb_Posets_chainPartition

namespace AppliedComb.Posets

/-- Theorem 6.18 (Dual of Dilworth's Theorem), Keller & Trotter p. 122: a finite poset of
height `h` has a partition into `h` antichains, and every antichain partition has at least
`h` parts. -/
theorem dual_dilworth (α : Type*) [PartialOrder α] [Fintype α] :
    (∃ A : Fin (height α) → Finset α, IsAntichainPartition A) ∧
    ∀ (k : ℕ) (A : Fin k → Finset α), IsAntichainPartition A → height α ≤ k := by sorry

end AppliedComb.Posets
