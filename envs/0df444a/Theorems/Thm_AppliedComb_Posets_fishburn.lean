-- Prove2me | Theorems.Thm_AppliedComb_Posets_fishburn
-- name    : AppliedComb.Posets.fishburn
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:07:07.666992+00:00
-- url     : https://prove2.me/theorems/720bcc53-de29-47e2-b17a-f339db188123
-- title:
--   Theorem 6.29 — Fishburn's Theorem: interval orders are the (2+2)-free posets
-- statement:
--   Let $\mathbf P = (X, P)$ be a finite poset. Then $\mathbf P$ is an interval order, i.e. there are closed real intervals $I(x) = [a_x, b_x]$, $x \in X$, with
--   $$x < y \text{ in } \mathbf P \iff b_x < a_y \quad (x, y \in X),$$
--   if and only if $\mathbf P$ excludes $\mathbf 2 + \mathbf 2$, i.e. $X$ contains no four points $x, y, z, w$ with $x < y$, $z < w$ and each of $x, y$ incomparable to each of $z, w$.
--
--   The theorem characterizes interval orders by a single forbidden four-point subposet.
--
--   **Formalization Note.** Stated for a finite type `α`: the book's construction of a representation (Section 6.7) indexes the down-sets as $D_1 \subsetneq \dots \subsetneq D_d$ with $d = |\mathcal D|$, which presumes finiteness, and the equivalence fails for some infinite posets (an uncountable well-ordered chain excludes $\mathbf 2 + \mathbf 2$ but has no real interval representation). "Excludes" is the absence of an order embedding of `Fin 2 ⊕ Fin 2` (disjoint-sum order), exactly the book's "no subposet isomorphic to $\mathbf 2 + \mathbf 2$".
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 129, Theorem 6.29

import Mathlib
import Definitions.Def_AppliedComb_Posets_intervalOrder

namespace AppliedComb.Posets

/-- Theorem 6.29 (Fishburn's Theorem), Keller & Trotter p. 129: a finite poset is an interval
order if and only if it excludes `2 + 2`. -/
theorem fishburn (α : Type*) [PartialOrder α] [Fintype α] :
    IsIntervalOrder α ↔ Excludes α TwoPlusTwo := by sorry

end AppliedComb.Posets
