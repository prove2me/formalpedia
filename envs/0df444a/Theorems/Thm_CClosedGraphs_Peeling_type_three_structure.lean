-- Prove2me | Theorems.Thm_CClosedGraphs_Peeling_type_three_structure
-- name    : CClosedGraphs.Peeling.type_three_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:25.051564+00:00
-- url     : https://prove2.me/theorems/83528d4c-65f5-43a3-b158-6431866e2220
-- title:
--   §2.1, p. 7 — properties A, B, C of a type-3 maximal clique, and maximality in G[N(v) ∩ N(u)]
-- statement:
--   Let $G$ be a finite simple graph, $W$ a set of vertices, $v\in W$, and let $K$ be a maximal clique of $G[W]$ of *type 3*: $v\in K$ and $K\setminus\{v\}$ is **not** a maximal clique of $G[W\setminus\{v\}]$. Then
--
--   1. (A) $K\setminus\{v\}\subseteq N(v)$;
--   2. (B) no vertex $w\in W\cap N(v)$ outside $K$ is adjacent to every vertex of $K\setminus\{v\}$;
--   3. (C) there is a vertex $u\in W$, $u\neq v$, not adjacent to $v$, which is adjacent to every vertex of $K\setminus\{v\}$, and for this $u$
--   $$K\setminus\{v\}\ \text{ is a maximal clique of }\ G[W\cap N(v)\cap N(u)].$$
--
--   These are the three properties of a type-3 clique stated on p. 7 of the paper, together with the consequence that $K\setminus\{v\}$ is maximal in $G[N(v)\cap N(u)]$; they are what lets one charge each type-3 clique to a pair $(u, \text{a maximal clique of } G[N(v)\cap N(u)])$.
--
--   **Formalization Note** "Property C: a vertex $u\notin N(v)$" is read as $u\in W\setminus(N(v)\cup\{v\})$, as in Figure 2 and in the sum (1); the paper's $N(\cdot)$ is the neighbourhood in the current graph $G[W]$, so all vertices are taken in $W$.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 7, §2.1, proof of Theorem 2.1 (properties A–C and the paragraph after them; Figure 2)

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace CClosedGraphs.Peeling
theorem type_three_structure {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Set V) (v : V) (hv : v ∈ W) (K : Finset V) (hK : K ∈ maxCliquesIn G W)
    (hvK : v ∈ K) (h3 : K.erase v ∉ maxCliquesIn G (W \ {v})) :
    (↑(K.erase v) : Set V) ⊆ G.neighborSet v ∧
    (∀ w ∈ W ∩ G.neighborSet v, w ∉ K → ¬ ∀ x ∈ K.erase v, G.Adj w x) ∧
    ∃ u ∈ W, u ≠ v ∧ ¬ G.Adj v u ∧ (∀ x ∈ K.erase v, G.Adj u x) ∧
      K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u) := by sorry
end CClosedGraphs.Peeling
