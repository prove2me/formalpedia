-- Prove2me | Theorems.Thm_AppliedComb_Graphs_triangle_free_chromatic
-- name    : AppliedComb.Graphs.triangle_free_chromatic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:03:49.549039+00:00
-- url     : https://prove2.me/theorems/0ac0fc8a-7db2-4255-826d-7ea5fc275fe2
-- title:
--   Proposition 5.25 — for every t ≥ 3 there is a graph with χ = t and ω = 2
-- statement:
--   For every integer $t \ge 3$ there is a finite graph $G_t$ with
--   $$\chi(G_t) = t \quad\text{and}\quad \omega(G_t) = 2,$$
--   where $\chi$ is the chromatic number and $\omega$ the clique number (the largest size of a set of pairwise adjacent vertices).
--
--   So chromatic number and clique number can be arbitrarily far apart: triangle-free graphs can need arbitrarily many colors (Kelly–Kelly; Mycielski).
--
--   **Formalization Note.** The graph lives on the vertex set $\{0, \dots, N-1\}$ (`Fin N`) for some $N$. $\chi$ is Mathlib's `chromaticNumber` ($\mathbb N_\infty$-valued, equal to the book's value on finite graphs) and $\omega$ is Mathlib's `cliqueNum`. Both equalities are exact, as on the page.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 85, Proposition 5.25 (clique number: p. 84)

import Mathlib

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 85, Proposition 5.25. For every `t ≥ 3` there is a (finite) graph `G_t`
with `χ(G_t) = t` and `ω(G_t) = 2`. The graph is taken on the vertex set `Fin N` for some `N`. -/
theorem triangle_free_chromatic (t : ℕ) (ht : 3 ≤ t) :
    ∃ (N : ℕ) (G : SimpleGraph (Fin N)), G.chromaticNumber = t ∧ G.cliqueNum = 2 := by sorry

end AppliedComb.Graphs
