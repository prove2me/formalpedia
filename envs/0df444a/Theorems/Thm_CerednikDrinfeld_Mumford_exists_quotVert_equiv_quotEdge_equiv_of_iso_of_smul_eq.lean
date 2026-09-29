-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_quotVert_equiv_quotEdge_equiv_of_iso_of_smul_eq
-- name    : CerednikDrinfeld.Mumford.exists_quotVert_equiv_quotEdge_equiv_of_iso_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/ba4aa1a2-d677-50f9-8a2d-f503fd0840f2
-- title:
--   Transport of the quotient graph datum along an equivariant isomorphism
-- statement:
--   Let $G_1,G_2$ be groups acting on types $W_1,W_2$, let $\mathcal T_1,\mathcal T_2$ be simple graphs on $W_1,W_2$ for which the actions send adjacent pairs to adjacent pairs (`GraphAction`), let $\varphi:G_1\to G_2$ be a surjective homomorphism and let $e:\mathcal T_1\simeq_g\mathcal T_2$ be a graph isomorphism with $e(g\cdot w)=\varphi(g)\cdot e(w)$ for all $g\in G_1$, $w\in W_1$. The assertion is that there exist bijections $e_V$ of vertex-orbit spaces $G_1\backslash W_1\to G_2\backslash W_2$ and $e_E$ of dart-orbit spaces $G_1\backslash\mathrm{Dart}(\mathcal T_1)\to G_2\backslash\mathrm{Dart}(\mathcal T_2)$ such that: $e_V[w]=[e\,w]$ and $e_E[d]=[e\,d]$ (the dart map induced by $e$); $e_E$ intertwines with $e_V$ the origin map $a$ and the terminus map $b$ of the quotient degeneracy data, and commutes with the reversal induced by $d\mapsto d^{\mathrm{op}}$; the dart maps of $e$ and of $e^{-1}$ are mutually inverse on $\mathrm{Dart}(\mathcal T_2)$; $\mathrm{Stab}_{G_2}(e\,w)=\varphi(\mathrm{Stab}_{G_1}(w))$ and $\mathrm{Stab}_{G_2}(e\,d)=\varphi(\mathrm{Stab}_{G_1}(d))$; if moreover $\varphi$ is injective then for every dart $d$ the two stabiliser cardinalities agree and the width of $e_E[d]$, namely $\mathrm{Nat.card}$ of the stabiliser of a chosen representative truncated into $\mathbb N^{+}$, equals that of $[d]$; $\mathcal T_2$-distance parities match, $\mathrm{dist}(e\,v_1,e\,w)\equiv\mathrm{dist}(v_1,w) \pmod 2$; for any $\tau_1:W_1\to\mathbb Z/2$ invariant under $G_1$ and any $\tau_2:W_2\to\mathbb Z/2$ with $\tau_2\circ e=\tau_1$, the function $\tau_2$ is $G_2$-invariant, $\tau_2$ of the origin of a chosen representative of $e_E x$ equals $\tau_1$ of the origin of a chosen representative of $x$, and $e_E$ restricts to a bijection between the subtypes where these values vanish; for all decidability instances on the two dart-orbit spaces, any type $E$, any family $orb:E\to G_1\backslash\mathrm{Dart}(\mathcal T_1)$ and any walk $p$ in $\mathcal T_1$, the cycle $\mathrm{walkCycle}$ of the image walk $p$ under $e$ read on $e_E\circ orb$ equals that of $p$ read on $orb$, where $\mathrm{walkCycle}$ sums over the darts of the walk the index $+1$ (resp. $-1$) according as the dart (resp. its reverse) lies in the given orbit; and, if $\mathcal T_1$ is acyclic, $\mathrm{pathCycle}$ of $e_E\circ orb$ at the base point $e\,v_0$ and the element $\varphi(g)$ equals $\mathrm{pathCycle}$ of $orb$ at $v_0$ and $g$.
--
--   This is the functoriality, or transport of structure, for the quotient graph of groups $G\backslash\mathcal T$ in the sense of Serre: an equivariant isomorphism of graphs over a surjection of groups identifies vertex and dart orbits together with the degeneracy maps, reversal, stabilisers, widths, distance parities and the cycle homomorphisms read off from chosen paths. It is used when an abstract coset graph is identified with the Bruhat–Tits tree, so that orbit data computed in one model can be read in the other, and it is cited in the analysis of invariant functions on the $p$-adic upper half plane in the Cerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_quotVert_equiv_quotEdge_equiv_of_iso_of_smul_eq.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_quotVert_equiv_quotEdge_equiv_of_iso_of_smul_eq
    {G₁ G₂ : Type} [Group G₁] [Group G₂] {W₁ W₂ : Type} [MulAction G₁ W₁] [MulAction G₂ W₂]
    (𝒯₁ : SimpleGraph W₁) (𝒯₂ : SimpleGraph W₂) [GraphAction G₁ 𝒯₁] [GraphAction G₂ 𝒯₂]
    (φ : G₁ →* G₂) (hφ : Function.Surjective φ)
    (e : 𝒯₁ ≃g 𝒯₂) (he : ∀ (g : G₁) (w : W₁), e (g • w) = φ g • e w) :
    ∃ (eV : QuotVert G₁ W₁ ≃ QuotVert G₂ W₂) (eE : QuotEdge G₁ 𝒯₁ ≃ QuotEdge G₂ 𝒯₂),
      (∀ w : W₁, eV (Quotient.mk (orbitRel G₁ W₁) w) = Quotient.mk (orbitRel G₂ W₂) (e w)) ∧
      (∀ d : 𝒯₁.Dart,
        eE (Quotient.mk (orbitRel G₁ 𝒯₁.Dart) d) = Quotient.mk (orbitRel G₂ 𝒯₂.Dart) (e.toHom.mapDart d)) ∧
      (∀ x : QuotEdge G₁ 𝒯₁, (quotientDegeneracyData G₂ 𝒯₂).a (eE x) = eV ((quotientDegeneracyData G₁ 𝒯₁).a x)) ∧
      (∀ x : QuotEdge G₁ 𝒯₁, (quotientDegeneracyData G₂ 𝒯₂).b (eE x) = eV ((quotientDegeneracyData G₁ 𝒯₁).b x)) ∧
      (∀ x : QuotEdge G₁ 𝒯₁, quotientReversal G₂ 𝒯₂ (eE x) = eE (quotientReversal G₁ 𝒯₁ x)) ∧
      (∀ d₂ : 𝒯₂.Dart, e.toHom.mapDart (e.symm.toHom.mapDart d₂) = d₂) ∧
      (∀ w : W₁, stabilizer G₂ (e w) = (stabilizer G₁ w).map φ) ∧
      (∀ d : 𝒯₁.Dart, stabilizer G₂ (e.toHom.mapDart d) = (stabilizer G₁ d).map φ) ∧
      (Function.Injective φ → ∀ d : 𝒯₁.Dart,
        Nat.card (stabilizer G₂ (e.toHom.mapDart d)) = Nat.card (stabilizer G₁ d) ∧
        (quotientDegeneracyData G₂ 𝒯₂).w (eE (Quotient.mk (orbitRel G₁ 𝒯₁.Dart) d)) =
          (quotientDegeneracyData G₁ 𝒯₁).w (Quotient.mk (orbitRel G₁ 𝒯₁.Dart) d)) ∧
      (∀ v₁ w : W₁, vertexType 𝒯₂ (e v₁) (e w) = vertexType 𝒯₁ v₁ w) ∧
      (∀ (τ₁ : W₁ → ZMod 2) (τ₂ : W₂ → ZMod 2), (∀ (g : G₁) (w : W₁), τ₁ (g • w) = τ₁ w) →
        (∀ w : W₁, τ₂ (e w) = τ₁ w) →
        (∀ (h : G₂) (w : W₂), τ₂ (h • w) = τ₂ w) ∧
        (∀ x : QuotEdge G₁ 𝒯₁, τ₂ (eE x).out.fst = τ₁ x.out.fst) ∧
        ∃ eEo : {x : QuotEdge G₁ 𝒯₁ // τ₁ x.out.fst = 0} ≃ {y : QuotEdge G₂ 𝒯₂ // τ₂ y.out.fst = 0},
          ∀ x : {x : QuotEdge G₁ 𝒯₁ // τ₁ x.out.fst = 0}, ((eEo x : {y : QuotEdge G₂ 𝒯₂ // τ₂ y.out.fst = 0}) : QuotEdge G₂ 𝒯₂) =
            eE (x : QuotEdge G₁ 𝒯₁)) ∧
      (∀ [DecidableEq (QuotEdge G₁ 𝒯₁)] [DecidableEq (QuotEdge G₂ 𝒯₂)] {E : Type} (orb : E → QuotEdge G₁ 𝒯₁)
        {u v : W₁} (p : 𝒯₁.Walk u v),
        walkCycle 𝒯₂ (fun i => eE (orb i)) (p.map e.toHom) = walkCycle 𝒯₁ orb p) ∧
      (𝒯₁.IsAcyclic → ∀ [DecidableEq (QuotEdge G₁ 𝒯₁)] [DecidableEq (QuotEdge G₂ 𝒯₂)] {E : Type}
        (orb : E → QuotEdge G₁ 𝒯₁) (v₀ : W₁) (g : G₁),
        pathCycle 𝒯₂ (fun i => eE (orb i)) (e v₀) (φ g) = pathCycle 𝒯₁ orb v₀ g) := by sorry
