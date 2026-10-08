-- Prove2me | Theorems.Thm_BasicPackArb_Main_theorem_1_6
-- name    : BasicPackArb.Main.theorem_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:29.850975+00:00
-- url     : https://prove2.me/theorems/46e52108-f292-4032-a4df-fdf2e890792e
-- title:
--   Theorem 1.6 — (D,S,π) has an M-basic packing of arborescences iff π is M-independent and (D,S,π) is M-connected
-- statement:
--   Let $D=(V,A)$ be a finite digraph (parallel arcs allowed), $S$ a finite set, $\pi:S\to V$ a placement of the elements of $S$ at vertices, and $M$ a matroid on $S$ with rank function $r_M$. Write $S_X=\pi^{-1}(X)$ and $S_v=\pi^{-1}(v)$, and $\rho_D(X)$ for the number of arcs entering $X$.
--
--   An **$M$-basic packing of arborescences** in $(D,S,\pi)$ is a family $(T_s)_{s\in S}$ of pairwise arc-disjoint arborescences in $D$, $T_s$ rooted at $\pi(s)$ and not necessarily spanning, such that for every vertex $v$ the set $\{s\in S:\ v\in V(T_s)\}$ is a base of $M$.
--
--   **Theorem 1.6.** There exists an $M$-basic packing of arborescences in $(D,S,\pi)$ if and only if
--
--   1. $\pi$ is $M$-independent: $S_v$ is independent in $M$ for every $v\in V$; and
--   2. $(D,S,\pi)$ is $M$-connected:
--   $$\rho_D(X)\ \ge\ r_M(S)-r_M(S_X)\qquad\text{for all non-empty }X\subseteq V.$$
--
--   With $M$ the free matroid on $S$, $|S|=k$, and every element placed at one vertex $r$, this is Edmonds' theorem on $k$ arc-disjoint spanning arborescences rooted at $r$. Through Frank's orientation theorem it also yields Katoh and Tanigawa's characterization of matroid-based rooted-tree packings in undirected graphs.
--
--   **Formalization Note** The packing is a family `T : S → Arborescence D` with `IsBasicPacking D π M T`, indexed by $S$ (so equal single-vertex arborescences at a vertex are distinct members). Arborescences are sub-digraphs given by a vertex set, an arc set inside $A$ and a root, with root in-degree $0$, in-degree $1$ elsewhere, and every vertex reachable from the root (equivalent to being a directed tree). The rank is `Matroid.eRk` in $\mathbb{N}_\infty$ and (3) is written $r_M(S)\le\rho_D(X)+r_M(S_X)$. The matroid's ground set is the whole root type; no other hypothesis is made.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 3, Theorem 1.6 (definitions pp. 1–3, (3) on p. 3; proof §2, pp. 4–5)

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph

namespace BasicPackArb.Main

/-- Theorem 1.6 (p. 3). Let `(D, S, π)` be a digraph with roots and `M` a matroid on `S`. There
exists an `M`-basic packing of arborescences in `(D, S, π)` if and only if `π` is `M`-independent
and `(D, S, π)` is `M`-connected. -/
theorem theorem_1_6 {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ) :
    (∃ T : S → Arborescence D, IsBasicPacking D π M T) ↔
      MIndependent π M ∧ MConnected D π M := by sorry

end BasicPackArb.Main
