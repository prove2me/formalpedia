-- Prove2me | Theorems.Thm_EdmondsMatching65_Polyhedron_theorem_M
-- name    : EdmondsMatching65.Polyhedron.theorem_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:45:15.455556+00:00
-- url     : https://prove2.me/theorems/e66b1a4a-e44d-4bc4-abbb-a4412f8eed1d
-- title:
--   Theorem (M), p. 127 — a matching is maximum iff a blossom-shrinking sequence {G_i} with (a)–(k) exists
-- statement:
--   **Theorem (M).** For a finite graph $G$ with real edge weights $c$, a matching $M$ is maximum (has the largest weight-sum among all matchings) if and only if there exists a sequence $\{G_i\}$, $i=0,\dots,n$, of graphs $G_i$ with matchings $M_i$, edge weights $w(e^i)$ and node weights $w(v^i)$ satisfying (a)–(k):
--
--   - (a) $G_0=G$, $w(e)=c$, $M_0=M$;
--   - (b) $w(v^i)\ge0$, and $w(v^i_1)+w(v^i_2)\ge w(e^i)$ for every edge of $G_i$;
--   - (c) for $i<n$, a circuit (blossom) $B_i$ in $G_i$ with $2a_i+1$ edges, $a_i$ of them in $M_i$;
--   - (d) $w(v^i_1)+w(v^i_2)=w(e^i)$ on $B_i$;
--   - (e) a node of $B_i$ meeting no edge of $M_i$ has the smallest weight $w(q^i)$ in $B_i$;
--   - (f) $G_{i+1}$ is $G_i$ with $B_i$ shrunk to a node $u^{i+1}$, and $M_{i+1}=M_i\cap G_{i+1}$;
--   - (g) weights are unchanged except at $u^{i+1}$ and on edges meeting it;
--   - (h) $w(u^{i+1})\le w(q^i)$ for the minimum $w(q^i)$ in $B_i$;
--   - (i) $w(e^{i+1})=w(e^i)-w(v^i)+w(q^i)$ for each edge meeting $u^{i+1}$ through $v^i\in B_i$;
--   - (j) $w(v^n_1)+w(v^n_2)=w(e^n)$ for $e^n\in M_n$;
--   - (k) $w(v^n)=0$ for every node of $G_n$ meeting no edge of $M_n$.
--
--   Theorem (M) is the combinatorial optimality condition behind Edmonds' weighted matching algorithm, proved on the way to Theorem (P).
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge. Weights $c$ may have any sign and $M$ need not be perfect.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 127, §4, Theorem (M)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_BlossomSequence

namespace EdmondsMatching65.Polyhedron

theorem theorem_M {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) (c : E → ℝ) (M : Finset E)
    (hM : IsMatching G M) :
    IsMaximumMatching G c M ↔ Nonempty (BlossomSequence G c M) := by sorry

end EdmondsMatching65.Polyhedron
