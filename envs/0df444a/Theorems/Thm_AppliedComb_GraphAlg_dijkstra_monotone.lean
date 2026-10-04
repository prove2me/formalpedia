-- Prove2me | Theorems.Thm_AppliedComb_GraphAlg_dijkstra_monotone
-- name    : AppliedComb.GraphAlg.dijkstra_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:36:52.624188+00:00
-- url     : https://prove2.me/theorems/b214e491-2770-4e2c-b1f9-0797d41a34cc
-- title:
--   Proposition 12.17 — Dijkstra's algorithm makes vertices permanent in nondecreasing order of δ
-- statement:
--   Run Dijkstra's algorithm (Algorithm 12.14) with root $r$ on a digraph with edge lengths in $\mathbb{N}_0$ and $n = |V|$ vertices. When the algorithm halts, let $\sigma = (v_1, v_2, \dots, v_n)$ be the sequence of permanent vertices. Then
--   $$\delta(v_1) \le \delta(v_2) \le \cdots \le \delta(v_n).$$
--
--   The claim holds for every run of the algorithm, i.e. for every way of choosing among temporary vertices of equal minimum $\delta$. It is the second ingredient of the correctness proof of Theorem 12.18.
--
--   **Formalization Note.** A halted state is a state `s` with `DijkstraRun G r (Fintype.card V) s`; the conclusion says that the list `s.σ.map s.δ` of values in $\mathbb{N}_0 \cup \{\infty\}$ (`ℕ∞`) is a chain for `≤`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 251, Proposition 12.17 (Algorithm 12.14, pp. 246–247)

import Mathlib
import Definitions.Def_AppliedComb_GraphAlg_Dijkstra

namespace AppliedComb.GraphAlg

/-- Keller–Trotter, p. 251, Proposition 12.17. When Dijkstra's algorithm (Algorithm 12.14) with
root `r` halts, at Step `n = |V|`, let `σ = (v₁, v₂, …, vₙ)`. Then
`δ(v₁) ≤ δ(v₂) ≤ ⋯ ≤ δ(vₙ)`. This holds for every run, i.e. for every admissible way of
breaking ties when a temporary vertex of minimum `δ` is chosen. -/
theorem dijkstra_monotone {V : Type*} [Fintype V] (G : WeightedDigraph V) (r : V)
    (s : DijkstraState V) (hs : DijkstraRun G r (Fintype.card V) s) :
    (s.σ.map s.δ).IsChain (· ≤ ·) := by sorry

end AppliedComb.GraphAlg
