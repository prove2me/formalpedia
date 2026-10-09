-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_x0_large
-- name    : CycleLengthsExp.ManyLengths.x0_large
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:51.40347+00:00
-- url     : https://prove2.me/theorems/56a4bc6f-3dc0-4220-84e1-df0b16d8e26b
-- title:
--   Theorem 2 proof — at least α²n/12 reachable path vertices
-- statement:
--   Let $0<\alpha\le1$, and let $G$ be an $\alpha$-expander on $n$ vertices. Take any set $S$ of $\lfloor\alpha n/4\rfloor$ vertices and any simple path $P$ in $G\setminus S$ with $\lceil\alpha n/4\rceil-1$ edges. Let $X_0$ be the vertices of $P$ reachable from $S$ by a simple path of at most $k(\alpha)$ edges whose internal vertices avoid both $S$ and $P$. If $\alpha n\ge12$, then
--   $$|X_0|\ge\frac{\alpha^2n}{12}.$$
--
--   This is the large starting set from which the proof extracts many distinct cycle lengths.
--
--   **Formalization Note** The source suppresses rounding in this estimate. The disclosed size condition $\alpha n\ge12$ rules out the case $S=\varnothing$, where $X_0=\varnothing$ and the printed inequality fails. The source's $S$ is the vertex set of a breadth-first-search tree; the counting argument uses its size and disjointness from $P$.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, pp. 13–14, proof of Theorem 2, definition of X₀ and 'The set X₀ is of size at least α²n/12'

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- The lower bound on `|X₀|` in the proof of Theorem 2, p. 14. -/
theorem x0_large (n : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hn : 12 ≤ α * (n : ℝ)) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) (S : Set (Fin n))
    (hS : S.ncard = Nat.floor (α * (n : ℝ) / 4))
    (u v : Fin n) (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length = Nat.ceil (α * (n : ℝ) / 4) - 1)
    (hdisj : ∀ w ∈ p.support, w ∉ S) :
    α ^ 2 * (n : ℝ) / 12 ≤ ((X0 α G S p).ncard : ℝ) := by sorry

end CycleLengthsExp.ManyLengths
