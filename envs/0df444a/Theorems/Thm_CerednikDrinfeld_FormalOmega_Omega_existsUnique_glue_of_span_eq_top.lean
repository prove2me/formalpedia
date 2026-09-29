-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top
-- name    : CerednikDrinfeld.FormalOmega.Omega.existsUnique_glue_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/0dec14e6-8461-5219-ab6e-c39df2307884
-- title:
--   Deligne data glue along a principal affine cover
-- statement:
--   Fix a commutative ring $\mathcal O$, a field $K$ that is an $\mathcal O$-algebra, an element $\pi \in \mathcal O$, and an $\mathcal O$-algebra $B$. Let $k \in \mathbb N$ and $f : \mathrm{Fin}\,k \to B$ be elements generating the unit ideal of $B$. For each $i$ let $C_i$ be an $\mathcal O$-algebra and $B$-algebra, compatibly (scalar tower over $\mathcal O$), which is a localisation of $B$ away from $f_i$, and for each pair $(i,j)$ let $C_{2,ij}$ be likewise a localisation of $B$ away from $f_i f_j$; let $\rho_1^{ij} : C_i \to C_{2,ij}$ and $\rho_2^{ij} : C_j \to C_{2,ij}$ be arbitrary $B$-algebra maps. Suppose given, for each $i$, an element $d_i$ of `Omega K π` at $C_i$, that is: a choice, for every full $\mathcal O$-lattice $M$ in $K^2$, of a $C_i$-submodule $\mathrm{line}(M) \subseteq C_i \otimes_{\mathcal O} M$ with invertible quotient, monotone for inclusions of lattices, equivariant for the scalar homotheties $\mathrm{scalarGL}(c)$, $c \in K^\times$, and satisfying the nondegeneracy condition at every prime of $C_i$ formulated with $\pi$. Assume the $d_i$ agree on overlaps, the transition maps $\rho_1^{ij}$, $\rho_2^{ij}$ being viewed as $\mathcal O$-algebra maps and the functoriality of `Omega K π` being pushforward of lines (span of the image under $\mathrm{rTensor}$). Then there is a unique Deligne datum $d_0$ over $B$ whose image under the structure map $B \to C_i$ equals $d_i$ for every $i$.
--
--   This is the Zariski sheaf property, for finite covers by principal opens, of Drinfeld's functor $\widehat\Omega$ on affine $\mathcal O$-algebras in its Deligne-datum description: $\widehat\Omega(B)$ is the equaliser of $\prod_i \widehat\Omega(B[1/f_i]) \rightrightarrows \prod_{i,j} \widehat\Omega(B[1/f_if_j])$. It is the gluing input for representing $\widehat\Omega$ by a scheme over $\mathcal O$ and for the comparison of the functor with its chart-wise models on the Čerednik–Drinfeld route.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.existsUnique_glue_of_span_eq_top
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B]
    {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (C : Fin k → Type) [∀ i, CommRing (C i)] [∀ i, Algebra 𝒪 (C i)] [∀ i, Algebra B (C i)]
    [∀ i, IsScalarTower 𝒪 B (C i)] [∀ i, IsLocalization.Away (f i) (C i)]
    (C₂ : Fin k → Fin k → Type) [∀ i j, CommRing (C₂ i j)] [∀ i j, Algebra 𝒪 (C₂ i j)] [∀ i j, Algebra B (C₂ i j)]
    [∀ i j, IsScalarTower 𝒪 B (C₂ i j)] [∀ i j, IsLocalization.Away (f i * f j) (C₂ i j)]
    (ρ₁ : ∀ i j, C i →ₐ[B] C₂ i j) (ρ₂ : ∀ i j, C j →ₐ[B] C₂ i j)
    (d : ∀ i, (Omega K π).obj (C i))
    (hd : ∀ i j, (Omega K π).map ((ρ₁ i j).restrictScalars 𝒪) (d i) = (Omega K π).map ((ρ₂ i j).restrictScalars 𝒪) (d j)) :
    ∃! d₀ : (Omega K π).obj B, ∀ i, (Omega K π).map (IsScalarTower.toAlgHom 𝒪 B (C i)) d₀ = d i := by sorry
