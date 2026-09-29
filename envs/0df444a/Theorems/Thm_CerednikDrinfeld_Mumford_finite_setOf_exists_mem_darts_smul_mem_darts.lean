-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts
-- name    : CerednikDrinfeld.Mumford.finite_setOf_exists_mem_darts_smul_mem_darts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/fb8f0545-9380-5500-9fda-694a9c0020fa
-- title:
--   Finite vertex stabilisers give finitely many walk-overlapping translations
-- statement:
--   Let $G$ be a group acting on a type $W$, let $\mathcal T$ be a simple graph on $W$, and suppose the action is by graph automorphisms in the sense of the project's `GraphAction` class, i.e. for every $g \in G$ and all $v, w \in W$, adjacency of $v$ and $w$ implies adjacency of $g \cdot v$ and $g \cdot w$; this induces the usual action of $G$ on the darts of $\mathcal T$. Assume that for every vertex $w \in W$ the stabiliser subgroup $\mathrm{Stab}_G(w)$ is finite. Let $u, v, u', v' \in W$ and let $P$ be a walk in $\mathcal T$ from $u$ to $v$ and $Q$ a walk from $u'$ to $v'$. Then the set of those $\gamma \in G$ for which there exists a dart $d$ occurring in the dart list of $Q$ such that either $\gamma \cdot d$ or its reversal $(\gamma \cdot d)^{\mathrm{symm}}$ occurs in the dart list of $P$ is a finite subset of $G$.
--
--   A finiteness statement for the set of group elements translating one walk so as to overlap another, in the setting of a discrete group acting on a graph (typically the Bruhat–Tits tree) with finite vertex stabilisers. It is what makes the sums over $G$ defining Mumford-style periods finite, and is cited in the computation of the period of $\Omega$ as a product over stabiliser widths and path cycles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.finite_setOf_exists_mem_darts_smul_mem_darts
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (stabilizer G w))
    {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    {γ : G | ∃ d ∈ Q.darts, γ • d ∈ P.darts ∨ (γ • d).symm ∈ P.darts}.Finite := by sorry
