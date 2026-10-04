-- Prove2me | Theorems.Thm_AppliedComb_Posets_sperner
-- name    : AppliedComb.Posets.sperner
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:06:29.304008+00:00
-- url     : https://prove2.me/theorems/36a4f69e-73f2-4398-b0e5-f5ae49778471
-- title:
--   Theorem 6.27 — Sperner's Theorem: width of the subset lattice
-- statement:
--   For an integer $t \ge 1$, let $\mathbf 2^t$ be the subset lattice: the family of all subsets of a $t$-element set $\{1, 2, \dots, t\}$, partially ordered by inclusion. Then the width of $\mathbf 2^t$, the largest size of a family of subsets no one of which contains another, is the size of a middle rank:
--   $$\operatorname{width}(\mathbf 2^t) = \binom{t}{\lfloor t/2 \rfloor}.$$
--
--   The statement is an equality: the family of all $\lfloor t/2 \rfloor$-element subsets is an antichain of that size, and no antichain is larger.
--
--   **Formalization Note.** The ground set $\{1, \dots, t\}$ is modelled by `Fin t` = $\{0, \dots, t-1\}$ (an order isomorphic copy), and $\mathbf 2^t$ by `Finset (Fin t)` with its inclusion order. Width is the definition `AppliedComb.Posets.width` (largest antichain). $\lfloor t/2 \rfloor$ is natural-number division `t / 2`. The hypothesis $t \ge 1$ is the book's.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 127, Theorem 6.27

import Mathlib
import Definitions.Def_AppliedComb_Posets_width

namespace AppliedComb.Posets

/-- Theorem 6.27 (Sperner's Theorem), Keller & Trotter p. 127: for `t ≥ 1` the width of the
subset lattice `2^t` (all subsets of a `t`-element set, ordered by inclusion; here
`Finset (Fin t)` ordered by `⊆`) equals `C(t, ⌊t/2⌋)`. -/
theorem sperner (t : ℕ) (ht : 1 ≤ t) :
    width (Finset (Fin t)) = Nat.choose t (t / 2) := by sorry

end AppliedComb.Posets
