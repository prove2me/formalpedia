-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge
-- name    : CerednikDrinfeld.Mumford.fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/49b5ba15-8531-5019-bc04-f3c9eb09aaf8
-- title:
--   Finite generation from a cofinite action on a connected graph
-- statement:
--   Let $G$ be a group acting on a type $W$, and let $\mathcal T$ be a simple graph with vertex set $W$ such that the action is by graph automorphisms in the sense of the class `GraphAction`: for every $g \in G$ and all $v,w \in W$, adjacency of $v$ and $w$ implies adjacency of $g \cdot v$ and $g \cdot w$. Assume that $\mathcal T$ is connected (`SimpleGraph.Connected`, so in particular $W$ is non-empty), that for every vertex $w \in W$ the stabiliser $\mathrm{Stab}_G(w)$ is finite, that the set of orbits `QuotVert G W`, i.e. the quotient of $W$ by the orbit relation of $G$, is finite, and that the set of orbits `QuotEdge G \mathcal T`, i.e. the quotient of the dart set `\mathcal T.Dart` (ordered adjacent pairs) by the induced orbit relation, is finite. Then $G$ is finitely generated, `Group.FG G`. Note that the finiteness hypothesis labelled `hE` concerns orbits of darts rather than of unoriented edges.
--
--   This is the standard finite-generation criterion for a group acting on a connected graph with finite vertex stabilisers and finitely many orbits of vertices and darts, as in Serre's theory of groups acting on trees. It is used in the Čerednik–Drinfeld part of the development, where it is cited by [`CerednikDrinfeld.BruhatTits.treeLattice_facts_map_evenPart`](thm.html#CerednikDrinfeld.BruhatTits.treeLattice_facts_map_evenPart) to produce finite generation for a group acting on the Bruhat–Tits tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hconn : 𝒯.Connected)
    (hstab : ∀ w : W, Finite (MulAction.stabilizer G w))
    (hV : Finite (QuotVert G W)) (hE : Finite (QuotEdge G 𝒯)) :
    Group.FG G := by sorry
