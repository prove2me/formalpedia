-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_exists_forall_map_eq_of_span_eq_top
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.exists_forall_map_eq_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/de170bce-b6ad-5ef5-88a6-08355f8d1e39
-- title:
--   Gluing G-points along a Zariski cover
-- statement:
--   Fix a prime $p$, a commutative ring $\mathcal O$, a commutative ring $O$ with an $\mathcal O$-algebra structure, and a moduli package $M$ for $p$ over $O$ (a rule assigning to each ring $B$, ring map $O \to B$ and witness that $p$ is nilpotent in $B$ a type, together with functorial transport along ring maps commuting with the structure maps), assumed to satisfy `M.IsZariskiSheaf`: over any such base, restriction to a cover by localisations away from elements generating the unit ideal is injective, and families agreeing on the double overlaps descend. Let $B$ be an $\mathcal O$-algebra in which $p$ is nilpotent, let $f_1,\dots,f_n \in B$ generate the unit ideal, and for each $i$ let $L_i$ be a localisation of $B$ away from $f_i$ and for each $i,j$ let $L_{2,ij}$ be a localisation away from $f_i f_j$, all carrying $\mathcal O$-algebra and $B$-algebra structures with the two compatible. Let $l_{ij} : L_i \to L_{2,ij}$ and $r_{ij} : L_j \to L_{2,ij}$ be $\mathcal O$-algebra maps which agree with the structure maps from $B$ on elements of $B$. Suppose given, for each $i$, a $G$-point $x_i$ over $L_i$, that is an $\mathcal O$-algebra map $\psi_i : O \to L_i$, a witness that $p$ is nilpotent in $L_i$ and an element of $M.\mathrm{obj}\,L_i\,\psi_i$, and suppose the pushforwards of $x_i$ along $l_{ij}$ and of $x_j$ along $r_{ij}$ coincide for all $i,j$. Then there is a $G$-point $y$ over $B$ whose pushforward along the structure map $B \to L_i$ equals $x_i$ for every $i$.
--
--   This is the existence (gluing) half of the Zariski sheaf property for the functor of $G$-points attached to a moduli package of special formal modules, the functor whose representability underlies the Čerednik–Drinfeld uniformisation; the separation half is proved separately. It is used in the construction of a natural rigidification transport over a cover, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedToG_natural_isRigTransport_of_cover`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedToG_natural_isRigTransport_of_cover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_exists_forall_map_eq_of_span_eq_top.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.exists_forall_map_eq_of_span_eq_top
    {p : ℕ} [Fact p.Prime] {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O] [Algebra 𝒪 O]
    {M : ModuliPackage.{0, 0} p O} (hM : M.IsZariskiSheaf)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (p : B))
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra 𝒪 (L i)] [∀ i, Algebra B (L i)] [∀ i, IsScalarTower 𝒪 B (L i)]
    [∀ i, IsLocalization.Away (f i) (L i)]
    (L₂ : Fin n → Fin n → Type) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra 𝒪 (L₂ i j)] [∀ i j, Algebra B (L₂ i j)]
    [∀ i j, IsScalarTower 𝒪 B (L₂ i j)] [∀ i j, IsLocalization.Away (f i * f j) (L₂ i j)]
    (l : ∀ i j, L i →ₐ[𝒪] L₂ i j) (r : ∀ i j, L j →ₐ[𝒪] L₂ i j)
    (hl : ∀ i j (b : B), l i j (algebraMap B (L i) b) = algebraMap B (L₂ i j) b)
    (hr : ∀ i j (b : B), r i j (algebraMap B (L j) b) = algebraMap B (L₂ i j) b)
    (x : ∀ i, ModuliPackage.GPoint 𝒪 M (L i))
    (hx : ∀ i j, (x i).map (l i j) = (x j).map (r i j)) :
    ∃ y : ModuliPackage.GPoint 𝒪 M B, ∀ i, y.map (IsScalarTower.toAlgHom 𝒪 B (L i)) = x i := by sorry
