-- Prove2me | Theorems.Thm_AppliedComb_Ramsey_high_girth_chromatic
-- name    : AppliedComb.Ramsey.high_girth_chromatic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:31:15.997239+00:00
-- url     : https://prove2.me/theorems/7f05b90c-7118-43ba-9847-9e30e6a74a10
-- title:
--   Theorem 11.7 (Erdős) — graphs with large girth and large chromatic number
-- statement:
--   The **girth** of a graph $G$ is the smallest integer $g$ for which $G$ contains a cycle on $g$ vertices; the girth of a forest is infinite. The **chromatic number** $\chi(G)$ is the least number of colours in a proper colouring of the vertices (adjacent vertices get different colours).
--
--   For every pair $g, t$ of integers with $g \ge 3$ there exists a finite simple graph $G$ with
--   $$\chi(G) > t \qquad\text{and}\qquad \operatorname{girth}(G) > g.$$
--
--   Such a graph has no short cycles, so every small neighbourhood looks like a tree, and yet it cannot be coloured with $t$ colours. The theorem is the chapter's showcase of the probabilistic method.
--
--   **Formalization Note.** The graph is a `SimpleGraph (Fin N)` for some $N$. The girth is Mathlib's `SimpleGraph.egirth`, valued in $\mathbb N \cup \{\infty\}$: the least length of a cycle, with length equal to the number of vertices on the cycle, and $\infty$ ($\top$) for a forest, exactly as on p. 234. Mathlib's `SimpleGraph.girth`, which is $0$ on forests, is deliberately not used. The chromatic number is `SimpleGraph.chromaticNumber`, also in $\mathbb N \cup \{\infty\}$ and finite on a finite graph. The parameter $t$ is taken in $\mathbb N$: for a negative integer $t$ the condition $\chi(G) > t$ is automatic, so nothing is lost.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 234, Theorem 11.7 (girth defined on the same page)

import Mathlib

namespace AppliedComb.Ramsey

/-- Theorem 11.7 (Erdős), Keller & Trotter p. 234: for all integers `g, t` with `g ≥ 3` there is
a (finite, simple) graph `G` with `χ(G) > t` and girth greater than `g`. The girth is Mathlib's
`SimpleGraph.egirth`, the least length of a cycle and `⊤` (infinite) for a forest, as on p. 234. -/
theorem high_girth_chromatic (g t : ℕ) (hg : 3 ≤ g) :
    ∃ (N : ℕ) (G : SimpleGraph (Fin N)),
      (t : ℕ∞) < G.chromaticNumber ∧ (g : ℕ∞) < G.egirth := by sorry

end AppliedComb.Ramsey
