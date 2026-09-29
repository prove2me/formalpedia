-- Prove2me | Theorems.Thm_ChvatalPolytopes_Neighbors_symmDiff_tree_certificate
-- name    : ChvatalPolytopes.Neighbors.symmDiff_tree_certificate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:22:22.154966+00:00
-- url     : https://prove2.me/theorems/86d64481-9fa9-423b-8581-67677b34e4ce
-- title:
--   Theorem 6.2 (i) — the weighting that makes two stable sets the only maximizers
-- statement:
--   Let $G=(V,E)$ be a finite graph, $Y,Z$ stable sets of $G$ with incidence vectors $y,z$, and $D=(Y-Z)\cup(Z-Y)$. Suppose the subgraph $H$ of $G$ induced by $D$ is connected, and let $T$ be a spanning tree of $H$. Let $c'_u$ ($u\in D$) and $m$ be nonnegative integers as specified by Lemma 6.1 for $T$ with the bicoloration $D=(Y-Z)\cup(Z-Y)$: $\sum_{u\in D}c'_ux_u\le m$ for every $x\in S(T)$, with equality exactly for the incidence vectors of $Y-Z$ and of $Z-Y$. Define $c\in\mathbb Z^V$ by
--   $$c_u=\begin{cases}c'_u & u\in D,\\ 1 & u\in Y\cap Z,\\ -1 & u\notin Y\cup Z.\end{cases}$$
--   Then
--   $$\sum_{u\in V}c_ux_u\le m+|Y\cap Z|\qquad\text{for all } x\in S(G),$$
--   with equality if and only if $x=y$ or $x=z$.
--
--   This is the certificate of the "if" part of Theorem 6.2: it exhibits the integer vector $c$ for which $y$ and $z$ are the only maximizers over $S(G)$.
--
--   **Formalization Note** The spanning tree $T$ is a `SimpleGraph` on the subtype of $D$ with $T\le H$ (so it has all vertices of $H$) and `T.IsTree`. The hypothesis on $c'$ and $m$ is the conclusion of Lemma 6.1 for $T$, $B=Y-Z$, $R=Z-Y$, written out. The connectedness of $H$ is kept as a hypothesis, as in the text, although it follows from the existence of $T$.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 149, §6, proof of Theorem 6.2, (i)

import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
import Definitions.Def_ChvatalPolytopes_Neighbors_IsBicoloration

namespace ChvatalPolytopes.Neighbors

/-- **The certificate of the "if" part of Theorem 6.2** (Chvátal 1975, p. 149, proof of
Theorem 6.2, (i)). Let `Y, Z` be stable sets of `G` with incidence vectors `y, z`, and let
`D = (Y − Z) ∪ (Z − Y)`. Suppose the subgraph `H` of `G` induced by `D` is connected, and let
`T` be a spanning tree of `H`. Let `c'_u` (`u ∈ D`) and `m` be as specified by Lemma 6.1 for `T`
with the bicoloration `D = (Y − Z) ∪ (Z − Y)`. Let `c_u = c'_u` for `u ∈ D`, `c_u = 1` if
`u ∈ Y ∩ Z` and `c_u = −1` if `u ∉ Y ∪ Z`. Then `Σ (c_u x_u : u ∈ V) ≤ m + |Y ∩ Z|` for all
`x ∈ S(G)`, with equality if and only if `x = y` or `x = z`. -/
theorem symmDiff_tree_certificate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y Z : Finset V)
    (hY : G.IsIndepSet (Y : Set V)) (hZ : G.IsIndepSet (Z : Set V))
    (hH : (G.induce (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V)).Connected)
    (T : SimpleGraph (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V))
    (hTsub : T ≤ G.induce (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V)) (hT : T.IsTree)
    (c' : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) → ℕ) (m : ℕ)
    (hc' : ∀ x ∈ stableVectors T,
      (∑ u, (c' u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c' u : ℝ) * x u = (m : ℝ) ↔
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Y \ Z) ∨
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Z \ Y))) :
    let c : V → ℤ := fun u =>
      if h : u ∈ (Y \ Z) ∪ (Z \ Y) then (c' ⟨u, by simpa using h⟩ : ℤ)
      else if u ∈ Y ∩ Z then 1 else -1
    ∀ x ∈ stableVectors G,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ) + ((Y ∩ Z).card : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) + ((Y ∩ Z).card : ℝ) ↔
        x = incidenceVector Y ∨ x = incidenceVector Z) := by sorry

end ChvatalPolytopes.Neighbors
