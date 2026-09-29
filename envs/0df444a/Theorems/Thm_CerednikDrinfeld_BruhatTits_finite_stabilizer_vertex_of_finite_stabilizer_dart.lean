-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart
-- name    : CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/e3616d43-054b-5cb4-bfa7-efd1b9952ef9
-- title:
--   Finite vertex stabilisers from finite dart stabilisers on the Bruhat–Tits tree
-- statement:
--   Let $R_0$ be a commutative domain which is a discrete valuation ring, with a field $K_0$ realised as its fraction field via an $R_0$-algebra structure, and assume the residue field `IsLocalRing.ResidueField R₀` is finite. The vertex set [`LT.LatticeTree.Vertex R₀ K₀`](def/LatticeTreeOrbital.html#L349) is the quotient of the full lattices in $K_0^2$ by homothety, and `BruhatTits.tree R₀ K₀` is the simple graph obtained by symmetrising the relation `VertRel`, which holds of two vertices when they admit representing full lattices $L$, $L'$ with `AdjacentLattice L L'`. Let $G$ be a group acting on this vertex set in such a way that the action preserves adjacency, i.e. $\mathcal{T}.\mathrm{Adj}(v,w)$ implies $\mathcal{T}.\mathrm{Adj}(g\cdot v, g\cdot w)$ for all $g$. Assume that for every dart $d$ of the tree (an edge together with an orientation) the stabiliser of $d$ in $G$ is finite. Then for every vertex $v$ the stabiliser of $v$ in $G$ is finite. Note that the dart hypothesis is assumed for all darts, whereas only those with first vertex $v$ enter the argument.
--
--   This supplies the 'finite vertex stabilisers' input required by the Mumford-curve/Čerednik–Drinfeld part of the development, where a group acting on the Bruhat–Tits tree of $K_0^2$ with finite dart stabilisers is shown to have finite vertex stabilisers; it is used in the construction of period data and the uniformisation statements for Mumford quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    (K₀ : Type) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (G : Type) [Group G] [MulAction G (LT.LatticeTree.Vertex R₀ K₀)] [GraphAction G (BruhatTits.tree R₀ K₀)]
    (hfinD : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (stabilizer G d))
    (v : LT.LatticeTree.Vertex R₀ K₀) : Finite (stabilizer G v) := by sorry
