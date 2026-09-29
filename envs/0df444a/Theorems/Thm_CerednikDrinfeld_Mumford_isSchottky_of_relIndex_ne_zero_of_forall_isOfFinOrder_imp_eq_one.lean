-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one
-- name    : CerednikDrinfeld.Mumford.isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/a98dcd7a-0740-5f5f-bcee-5aef3d9d5fc9
-- title:
--   Torsion-free finite-index subgroups of inversion-free tree lattices are Schottky
-- statement:
--   Let $G$ be a group acting on a type $W$, and let $\mathcal T$ be a simple graph on $W$ for which the action is by graph automorphisms (adjacency of $v,w$ implies adjacency of $g\cdot v, g\cdot w$), with $\mathcal T$ a tree. Let $\Gamma \le G$ be a subgroup such that: for every vertex $w$ the stabiliser of $w$ in $\Gamma$ is finite; the quotient of $W$ by the orbit relation of $\Gamma$ is finite, and likewise the quotient of the dart type $\mathcal T.\mathrm{Dart}$ by the orbit relation of $\Gamma$; and no element of $\Gamma$ reverses a dart, i.e. $g\cdot d \ne \bar d$ for all $g \in \Gamma$ and all darts $d$. Let $N \le \Gamma$ be a subgroup whose relative index in $\Gamma$ is nonzero (finite index in $\Gamma$), and suppose every element of $N$ of finite order equals $1$. Then $N$, acting on $\mathcal T$, satisfies `IsSchottky`: every vertex stabiliser in $N$ is trivial; $g\cdot d \ne \bar d$ for every $g \in N$ and every dart $d$; and the quotients of $W$ and of $\mathcal T.\mathrm{Dart}$ by the orbit relations of $N$ are both finite.
--
--   This is the standard passage from a cocompact tree lattice with finite stabilisers and without inversions to a Schottky group, in the sense used by Mumford in the uniformisation of curves over local fields: freeness on vertices follows from torsion-freeness. It is used in the construction of the Čerednik–Drinfel'd quotients, via [`CerednikDrinfeld.exists_isSchottky_le_map_normal_relIndex_ne_zero_of_even`](thm.html#CerednikDrinfeld.exists_isSchottky_le_map_normal_relIndex_ne_zero_of_even).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (h𝒯 : 𝒯.IsTree)
    (Γ : Subgroup G)
    (hstab : ∀ w : W, Finite (MulAction.stabilizer (↥Γ) w))
    (hV : Finite (QuotVert (↥Γ) W)) (hE : Finite (QuotEdge (↥Γ) 𝒯))
    (hinv : ∀ g ∈ Γ, ∀ d : 𝒯.Dart, g • d ≠ d.symm)
    (N : Subgroup G) (hle : N ≤ Γ) (hidx : N.relIndex Γ ≠ 0)
    (htf : ∀ g ∈ N, IsOfFinOrder g → g = 1) :
    IsSchottky (↥N) 𝒯 := by sorry
