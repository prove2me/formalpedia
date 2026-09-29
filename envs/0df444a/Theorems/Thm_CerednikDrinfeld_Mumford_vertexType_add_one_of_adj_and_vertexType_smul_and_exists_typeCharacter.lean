-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
-- name    : CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/8e477244-ecb5-5489-bbc9-ee57165e45e4
-- title:
--   Vertex types on a connected bipartite graph with automorphisms
-- statement:
--   Let $G$ be a group acting on a type $W$, let $\mathcal T$ be a simple graph on $W$, and assume the action is by graph maps in the sense of the class `GraphAction`: for every $g \in G$ and all $v,w \in W$, if $v$ and $w$ are adjacent then so are $g \cdot v$ and $g \cdot w$. Assume further that $\mathcal T$ is connected and $2$-colourable, and fix a base vertex $w_0 \in W$. Write $\tau(w) =$ `vertexType 𝒯 w₀ w` for the class in $\mathbb Z/2$ of the graph distance $d_{\mathcal T}(w_0,w)$. Then three assertions hold simultaneously: (a) for all $x,y \in W$ adjacent in $\mathcal T$, $\tau(y) = \tau(x) + 1$; (b) for all $g \in G$ and $w \in W$, $\tau(g \cdot w) = \tau(g \cdot w_0) + \tau(w)$; and (c) there exists a group homomorphism $\varepsilon \colon G \to \mathrm{Multiplicative}(\mathbb Z/2)$ such that $\mathrm{toAdd}(\varepsilon(g)) = \tau(g \cdot w_0)$ for every $g \in G$, and whose kernel equals the subgroup `typePreserving G 𝒯 w₀` of those $g \in G$ with $\tau(g \cdot w) = \tau(w)$ for all $w \in W$.
--
--   These are the basic laws of the type (parity-of-distance) function on a connected bipartite graph with a group of automorphisms, as used for the Bruhat–Tits tree of $\mathrm{PGL}_2$ over a local field: adjacent vertices have opposite type, the type shifts by a character, and the type character cuts out the type-preserving subgroup (of index at most $2$). The result is invoked throughout the Čerednik–Drinfeld/Mumford uniformisation part of the development, where type-preserving subgroups of the relevant arithmetic groups govern the combinatorics of the quotient graph.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter.lean

import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordPeriod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W) :
    (∀ x y : W, 𝒯.Adj x y → vertexType 𝒯 w₀ y = vertexType 𝒯 w₀ x + 1) ∧
    (∀ (g : G) (w : W), vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ (g • w₀) + vertexType 𝒯 w₀ w) ∧
    (∃ ε : G →* Multiplicative (ZMod 2),
      (∀ g : G, Multiplicative.toAdd (ε g) = vertexType 𝒯 w₀ (g • w₀)) ∧ ε.ker = typePreserving G 𝒯 w₀) := by sorry
