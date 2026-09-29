-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul
-- name    : CerednikDrinfeld.Mumford.GraphAction.dist_smul_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/a74ae892-05b2-5a4e-a882-9f1708fcf708
-- title:
--   Graph actions preserve the graph distance
-- statement:
--   Let $G$ be a group acting on a type $W$, and let $\mathcal T$ be a simple graph with vertex set $W$. Assume the action satisfies the project's `GraphAction` condition, namely that for every $g \in G$ and all vertices $v, w$, adjacency of $v$ and $w$ in $\mathcal T$ implies adjacency of $g \cdot v$ and $g \cdot w$; note that only preservation of adjacency in this one direction is assumed, no reflection of adjacency and no surjectivity. Then for every $g \in G$ and all vertices $x, y \in W$ the graph distances satisfy $\operatorname{dist}_{\mathcal T}(g \cdot x, g \cdot y) = \operatorname{dist}_{\mathcal T}(x, y)$, where $\operatorname{dist}_{\mathcal T}$ is Mathlib's graph distance, the least length of a walk joining the two vertices, with the convention that the distance is $0$ when the two vertices lie in different connected components. In particular each $g$ acts as an isometry for the graph metric, and vertices in the same component are carried to vertices in the same component.
--
--   This is the elementary statement that a group acting on a graph by adjacency-preserving maps acts by isometries of the graph distance. It is used in the Čerednik–Drinfel'd part of the development to speak of distances on the Bruhat–Tits tree invariantly: it is cited for the computation of the distance between the standard vertex and its translate by an integral matrix of given determinant, and in the comparison of a valuation of a cross-ratio of Möbius-transformed points with a power attached to walk overlap.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.Mumford.GraphAction.dist_smul_smul
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W)
    [CerednikDrinfeld.Mumford.GraphAction G 𝒯] (g : G) (x y : W) :
    𝒯.dist (g • x) (g • y) = 𝒯.dist x y := by sorry
