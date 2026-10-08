-- Prove2me | Theorems.Thm_EHRR10_Larman_diameter_le_larman
-- name    : EHRR10.Larman.diameter_le_larman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:46:43.005486+00:00
-- url     : https://prove2.me/theorems/2472a3f5-f804-4f87-a903-8b1a33281ee9
-- title:
--   Larman's bound 2^(d−1)·n in the base abstraction
-- statement:
--   Let $d\ge 1$ and $n$ be natural numbers, and let $G$ be any graph in the base abstraction $\mathcal B_{d,n}$. Thus its vertices are distinct $d$-subsets of an $n$-element label set, and every pair is joined through vertices containing their common labels. Every pair of vertices $u,v$ can be joined by a path of at most $2^{d-1}n$ edges. Equivalently, the diameter of every graph in $\mathcal B_{d,n}$ obeys
--
--   $$
--   \operatorname{diam}(G)\le 2^{d-1}n.
--   $$
--
--   This is the Larman upper bound that Eisenbrand, Hähnle, Razborov and Rothvoß announce for their combinatorial abstraction. For a fixed positive dimension, it is linear in the number of labels.
--
--   **Formalization Note** The paper writes the displayed bound using $\Delta_u(d,n)$, then says that it continues to hold in the base abstraction. The Lean statement spells this out for every $G\in\mathcal B_{d,n}$ and every pair of its vertices. The explicit condition $d\ge1$ makes the exponent $d-1$ ordinary subtraction. An existential walk of bounded length expresses the distance bound without choosing a default value for the diameter of an empty or disconnected graph.
-- source:
--   Eisenbrand, Hähnle, Razborov, Rothvoß, Diameter of Polyhedra: Limits of Abstraction, Dagstuhl Seminar Proceedings 10211 (2010), p. 3, sentence beginning 'At the same time the bound of Kalai and Kleitman'; http://drops.dagstuhl.de/opus/volltexte/2010/2724

import Mathlib
import Definitions.Def_EHRR10_LowerBound_BaseAbstraction

namespace EHRR10.Larman

/-- Larman's bound in the base abstraction (Dagstuhl 10211, 2010, p. 3): for `d ≥ 1`, any two
vertices of a graph in `𝓑_{d,n}` are joined by a walk with at most `2^(d-1) * n` edges,
i.e. `D(d, n) ≤ 2^(d-1) · n`. -/
theorem diameter_le_larman (d n : ℕ) (hd : 1 ≤ d)
    (V : Finset (Finset (Fin n))) (G : SimpleGraph V) (hG : EHRR10.LowerBound.InB d n V G)
    (u v : V) :
    ∃ p : G.Walk u v, p.length ≤ 2 ^ (d - 1) * n := by sorry

end EHRR10.Larman
