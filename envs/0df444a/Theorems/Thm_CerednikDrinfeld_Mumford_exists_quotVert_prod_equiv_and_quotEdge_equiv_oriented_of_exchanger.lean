-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger
-- name    : CerednikDrinfeld.Mumford.exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/64a1b953-c017-53e9-9e5d-2f841832f976
-- title:
--   Splitting quotients of a two-coloured graph by a type-exchanging subgroup
-- statement:
--   Let $G$ be a group acting on a type $W$, and let $\mathcal T$ be a simple graph on $W$ for which the action is by graph automorphisms (each $g$ carries adjacent vertices to adjacent vertices). Assume $\mathcal T$ is connected and $2$-colourable, fix $w_0 \in W$, and write $\mathrm{type}(w) = d_{\mathcal T}(w_0,w) \bmod 2 \in \mathbb Z/2$ and $T = \mathrm{typePreserving}$, the subgroup of those $g \in G$ with $\mathrm{type}(g\cdot w) = \mathrm{type}(w)$ for all $w$. Let $\Delta \le G$ be a subgroup containing an element $\gamma_0 \notin T$, and put $\Delta_+ = \Delta \sqcap T$. The assertion is that there exist bijections $\varepsilon_V : (\Delta\backslash W) \times \mathrm{Fin}\,2 \simeq \Delta_+\backslash W$ and $\varepsilon_E : \Delta\backslash \mathrm{Dart}(\mathcal T) \simeq \{e \in \Delta_+\backslash\mathrm{Dart}(\mathcal T) : \mathrm{type}(\mathrm{fst}(e.\mathrm{out})) = 0\}$, where $e.\mathrm{out}$ is the chosen representative dart of $e$, such that: for $w$ of type $i \in \{0,1\}$, $\varepsilon_V(\Delta w, i) = \Delta_+ w$; for a dart $d$ whose source has type $0$, $\varepsilon_E(\Delta d) = \Delta_+ d$; for every $e \in \Delta\backslash\mathrm{Dart}(\mathcal T)$ the source and target maps $a, b$ of the quotient degeneracy data satisfy $a(\varepsilon_E e) = \varepsilon_V(a(e),0)$ and $b(\varepsilon_E e) = \varepsilon_V(b(e),1)$; and for every dart $d$, the stabilisers of $d$ in $\Delta$ and in $\Delta_+$ have equal cardinality.
--
--   This is the combinatorial step, in the style of Serre's theory of quotient graphs, that compares the quotient of a two-coloured graph by a subgroup $\Delta$ containing a type-reversing element with the quotient by its type-preserving part $\Delta_+$ of index $2$: vertices double up with a type label, darts are normalised to those running from type $0$ to type $1$, and edge widths (stabiliser orders) are unchanged. It feeds the construction of the degeneracy data and the Mumford-period/Čerednik–Drinfeld comparisons that cite it, in particular the statements on realisations of quotient vertex and dart data and on descent intertwining.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger.lean

import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W)
    (Δ : Subgroup G) (γ₀ : G) (hγ₀ : γ₀ ∈ Δ) (hγ₀' : γ₀ ∉ typePreserving G 𝒯 w₀) :
    ∃ (εV : QuotVert (↥Δ) W × Fin 2 ≃ QuotVert (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W)
      (εE : QuotEdge (↥Δ) 𝒯 ≃
        {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}),

      (∀ w : W, vertexType 𝒯 w₀ w = 0 →
        εV (Quotient.mk (MulAction.orbitRel (↥Δ) W) w, 0) =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) w) ∧
      (∀ w : W, vertexType 𝒯 w₀ w = 1 →
        εV (Quotient.mk (MulAction.orbitRel (↥Δ) W) w, 1) =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) w) ∧

      (∀ d : 𝒯.Dart, vertexType 𝒯 w₀ d.fst = 0 →
        ((εE (Quotient.mk (MulAction.orbitRel (↥Δ) 𝒯.Dart) d) :
            {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}) :
            QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯.Dart) d) ∧

      (∀ e : QuotEdge (↥Δ) 𝒯,
        (quotientDegeneracyData (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯).a ((εE e : {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}) : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
          εV ((quotientDegeneracyData (↥Δ) 𝒯).a e, 0) ∧
        (quotientDegeneracyData (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯).b ((εE e : {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}) : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
          εV ((quotientDegeneracyData (↥Δ) 𝒯).b e, 1)) ∧

      (∀ d : 𝒯.Dart,
        Nat.card (MulAction.stabilizer (↥Δ) d) = Nat.card (MulAction.stabilizer (↥(Δ ⊓ typePreserving G 𝒯 w₀)) d)) := by sorry
