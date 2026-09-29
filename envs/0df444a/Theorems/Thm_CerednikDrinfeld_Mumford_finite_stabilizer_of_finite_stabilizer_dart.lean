-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart
-- name    : CerednikDrinfeld.Mumford.finite_stabilizer_of_finite_stabilizer_dart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/14a73495-36cb-533a-806b-c625133695f9
-- title:
--   Finite vertex stabilisers from finite dart stabilisers
-- statement:
--   Let $G$ be a group acting on a type $W$, let $\mathcal{T}$ be a simple graph with vertex type $W$, and assume the action is by graph automorphisms in the sense of the project's class `GraphAction`, whose single field asserts that for every $g : G$ and all $v, w : W$, adjacency $\mathcal{T}.\mathrm{Adj}\ v\ w$ implies $\mathcal{T}.\mathrm{Adj}\ (g \cdot v)\ (g \cdot w)$. Let $v : W$ be a vertex whose neighbour set $\mathcal{T}.\mathrm{neighborSet}\ v$ is finite and nonempty, and suppose that for every dart $d$ of $\mathcal{T}$ (an ordered pair of adjacent vertices) with first vertex equal to $v$, the stabiliser of $d$ in $G$, for the induced componentwise action of $G$ on darts, is a finite subgroup. The conclusion is that the stabiliser of $v$ in $G$ is finite. The nonemptiness hypothesis is genuinely needed: at an isolated vertex there are no darts issuing from $v$, so the dart hypothesis is vacuous while the vertex stabiliser may be infinite.
--
--   This is the elementary orbit–stabiliser step, familiar from the theory of groups acting on graphs, that upgrades finiteness of edge (dart) stabilisers to finiteness of vertex stabilisers at a vertex of finite positive valency. It is applied on the Bruhat–Tits tree, where every vertex has $q+1$ neighbours, in [`CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart`](thm.html#CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.finite_stabilizer_of_finite_stabilizer_dart
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (v : W) (hfin : (𝒯.neighborSet v).Finite) (hne : (𝒯.neighborSet v).Nonempty)
    (hD : ∀ d : 𝒯.Dart, d.fst = v → Finite (stabilizer G d)) :
    Finite (stabilizer G v) := by sorry
