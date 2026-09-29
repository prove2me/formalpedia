-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two
-- name    : CerednikDrinfeld.Mumford.exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/1af99c6a-9f2b-54ef-929a-079d62405541
-- title:
--   Type-preserving subgroup is the kernel of a ℤ/2-character
-- statement:
--   Let $G$ be a group acting on a type $W$, and let $\mathcal{T}$ be a simple graph on $W$ whose adjacency relation is preserved by the action (the hypothesis `Mumford.GraphAction G 𝒯`: for every $g \in G$ and vertices $v,w$, adjacency of $v$ and $w$ implies adjacency of $g \cdot v$ and $g \cdot w$). Assume $\mathcal{T}$ is connected and $2$-colourable, and fix a base vertex $w_0 \in W$. Write $\mathrm{type}(w) = (\mathrm{dist}_{\mathcal{T}}(w_0, w) \bmod 2) \in \mathbb{Z}/2$ for the parity of the graph distance from $w_0$, and let $\mathrm{typePreserving}$ be the subgroup of those $g \in G$ with $\mathrm{type}(g \cdot w) = \mathrm{type}(w)$ for every vertex $w$. The assertion is twofold: first, there exists a group homomorphism $\varphi : G \to \mathrm{Multiplicative}(\mathbb{Z}/2)$ whose kernel is exactly this type-preserving subgroup; second, the index of the type-preserving subgroup in $G$ divides $2$ (so it is $1$ or $2$, and in particular finite).
--
--   This is the standard statement that a group acting on a connected bipartite graph (typically the Bruhat–Tits tree of $\mathrm{PGL}_2$ over a local field, where the character is the parity of the valuation of the determinant) has its type-preserving subgroup cut out by a character of order dividing $2$. It is used in the Čerednik–Drinfel'd part of the development to transfer finiteness and Schottky-type properties between a group and its type-preserving part, being cited by [`CerednikDrinfeld.Omega.exists_forall_exists_smul_mem_affinoid_of_relIndex_ne_zero`](thm.html#CerednikDrinfeld.Omega.exists_forall_exists_smul_mem_affinoid_of_relIndex_ne_zero) and [`CerednikDrinfeld.Omega.isSchottky_map_of_relIndex_ne_zero_of_forall_isOfFinOrder`](thm.html#CerednikDrinfeld.Omega.isSchottky_map_of_relIndex_ne_zero_of_forall_isOfFinOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [Mumford.GraphAction G 𝒯]
    (hconn : 𝒯.Connected) (hbip : 𝒯.Colorable 2) (w₀ : W) :
    (∃ φ : G →* Multiplicative (ZMod 2), φ.ker = Mumford.typePreserving G 𝒯 w₀) ∧
      (Mumford.typePreserving G 𝒯 w₀).index ∣ 2 := by sorry
