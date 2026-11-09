-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_observation_2
-- name    : ArcKayles192.PSPACE.observation_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:16.278887+00:00
-- url     : https://prove2.me/theorems/309f0a4b-2712-47f9-8917-154bf634af40
-- title:
--   Observation 2: from a position of value $n$ every value $i<n$ is reachable in one move, and $n$ is not
-- statement:
--   Let $G$ be a simple graph and $S$ a position of Arc Kayles on it, with Sprague–Grundy value $\mathrm{sg}(G,S)=n$. Then
--
--   1. for every $i<n$ there is a legal move $uv$ ($u,v\in S$, $uv\in E(G)$) with $\mathrm{sg}(G,S\setminus\{u,v\})=i$;
--   2. no legal move $uv$ satisfies $\mathrm{sg}(G,S\setminus\{u,v\})=n$.
--
--   This is the mex property of the value function, used in Lemmas 3 and 4.
--
--   Differences from the source:
--   - encoding: a position is a graph; isolated vertices are removed automatically (p.3) → a position is a finite set S of remaining vertices of an ambient simple graph G, the current graph being G[S]; isolated vertices stay in S; reason: an isolated vertex carries no move, so outcomes and values are unchanged; every finite graph H is the position (H, all vertices), and every position is the finite graph G[S]
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.2, Observation 2

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game

namespace ArcKayles192.PSPACE

/-- **Observation 2** (p.2). From any position of value `n`, and for every `i < n`, there is a
move to a position of value `i`, but there is no move to a position of value `n`. -/
theorem observation_2 {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    (∀ i < sg G S, ∃ u v, u ∈ S ∧ v ∈ S ∧ G.Adj u v ∧ sg G (S \ {u, v}) = i) ∧
    (∀ u v, u ∈ S → v ∈ S → G.Adj u v → sg G (S \ {u, v}) ≠ sg G S) := by sorry

end ArcKayles192.PSPACE
