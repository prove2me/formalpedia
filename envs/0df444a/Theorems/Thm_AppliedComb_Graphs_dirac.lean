-- Prove2me | Theorems.Thm_AppliedComb_Graphs_dirac
-- name    : AppliedComb.Graphs.dirac
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:02:18.515856+00:00
-- url     : https://prove2.me/theorems/d897c927-803d-4bd7-bc09-74e099f02e77
-- title:
--   Theorem 5.18 — Dirac: minimum degree ⌈n/2⌉ forces a hamiltonian cycle
-- statement:
--   Let $G = (V, E)$ be a graph on $n = |V| \ge 1$ vertices in which every vertex has at least $\lceil n/2 \rceil$ neighbours:
--   $$\deg_G(v) \ge \left\lceil \tfrac{n}{2} \right\rceil \quad \text{for every } v \in V.$$
--   Then $G$ is hamiltonian: there is a sequence $(x_1, \dots, x_n)$ listing every vertex exactly once with $x_i x_{i+1} \in E$ for $i < n$ and $x_1 x_n \in E$.
--
--   Dirac's condition (1952) is the classical sufficient condition for hamiltonicity; deciding hamiltonicity in general has no known efficient method.
--
--   **Formalization Note.** $\lceil n/2 \rceil$ is written `(n + 1) / 2` in $\mathbb N$, and $n$ is tied to the graph by `Fintype.card V = n`. "Hamiltonian" is the book's notion (`AppliedComb.Graphs.IsHamiltonian`), under which $K_2$ is hamiltonian; with Mathlib's `IsHamiltonianCycle` the statement would be false at $n = 2$. The vertex type is assumed nonempty, since the book's proof takes $n$ to be a positive integer and the empty graph has no hamiltonian cycle. At $n = 1$ the degree hypothesis cannot hold, exactly as on the page.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 80, Theorem 5.18 (definition of hamiltonian on p. 79)

import Mathlib
import Definitions.Def_AppliedComb_Graphs_IsHamiltonian

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 80, Theorem 5.18 (Dirac). If `G` is a graph on `n` vertices and each
vertex of `G` has at least `⌈n/2⌉` neighbors, then `G` is hamiltonian (book's definition,
p. 79). `⌈n/2⌉` is written `(n + 1) / 2` in `ℕ`. The vertex set is nonempty (the book's proof
takes `n` to be a positive integer). -/
theorem dirac {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n) (hdeg : ∀ v : V, (n + 1) / 2 ≤ G.degree v) :
    IsHamiltonian G := by sorry

end AppliedComb.Graphs
