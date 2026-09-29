-- Prove2me | Theorems.Thm_AlgebraicGeometry_valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection
-- name    : AlgebraicGeometry.valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/dc3fd838-f175-541b-ae09-6addbe43e83f
-- title:
--   Reduction to the zero section forces v(g(b)-ε(b))<1
-- statement:
--   Let $A$ be a commutative ring equipped with an algebra structure on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $X$ be a scheme and $f : X \to \operatorname{Spec} A$ a morphism admitting a section $\mathrm{zero}$, i.e. $\mathrm{zero}$ followed by $f$ is the identity of $\operatorname{Spec} A$. Let $B$ be an $A$-bialgebra and $c : \operatorname{Spec} B \to X$ a closed immersion with $c$ followed by $f$ equal to $\operatorname{Spec}$ of the structure map $A \to B$, and such that $\operatorname{Spec}$ of the counit $\epsilon : B \to A$ followed by $c$ equals $\mathrm{zero}$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$, $\rho : A \to Pl$ a ring map whose composite with the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $A \to \overline{\mathbb{Q}}$, and $\pi_k : Pl \to k$ a ring map to a field $k$ with $A$-algebra structure, such that the structure map $A \to k$ is $\pi_k \circ \rho$ and $\ker \pi_k$ is the maximal ideal of the local ring $Pl$. Finally let $g : B \to \overline{\mathbb{Q}}$ be an $A$-algebra map and let $z$ be a morphism $\operatorname{Spec} Pl \to X$ with $z$ followed by $f$ equal to $\operatorname{Spec} \rho$ (an element of the subtype `SchemeHomOver`), subject to: $\operatorname{Spec} g$ followed by $c$ equals $\operatorname{Spec}(Pl \hookrightarrow \overline{\mathbb{Q}})$ followed by $z$, and $\operatorname{Spec} \pi_k$ followed by $z$ equals $\operatorname{Spec}(A \to k)$ followed by $\mathrm{zero}$. Then for every $b \in B$ the valuation attached to $Pl$ satisfies $v\bigl(g(b) - \epsilon(b)_{\overline{\mathbb{Q}}}\bigr) < 1$, where $\epsilon(b)_{\overline{\mathbb{Q}}}$ denotes the image of the counit $\epsilon(b) \in A$ in $\overline{\mathbb{Q}}$.
--
--   This is the valuative reading of a point of a closed affine subscheme (the spectrum of a bialgebra, with unit section given by the counit) lying over a valuation subring of $\overline{\mathbb{Q}}$: if the $Pl$-point reduces to the zero section modulo the maximal ideal, then all coordinates of the associated $\overline{\mathbb{Q}}$-point are congruent to their counit values, i.e. lie in the maximal ideal after subtraction. It is used in the analysis of points of $p$-divisible groups and Tate modules attached to the modular curve, where reduction to the zero section has to be converted into valuation estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection
    (A : Type) [CommRing A] [Algebra A (AlgebraicClosure ℚ)]

    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (zero : Spec (CommRingCat.of A) ⟶ X) (hzero : zero ≫ f = 𝟙 _)
    (B : Type) [CommRing B] [Bialgebra A B]
    (c : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion c]
    (hc : c ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (hunit : Spec.map (CommRingCat.ofHom ((Bialgebra.counitAlgHom A B : B →ₐ[A] A) : B →+* A)) ≫ c = zero)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (k : Type) [Field k] [Algebra A k] (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)
    (hπk : RingHom.ker πk = IsLocalRing.maximalIdeal ↥Pl)

    (g : B →ₐ[A] AlgebraicClosure ℚ) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f)
    (hz : Spec.map (CommRingCat.ofHom ((g : B →ₐ[A] AlgebraicClosure ℚ) : B →+* AlgebraicClosure ℚ)) ≫ c =
      Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1)
    (hred : Spec.map (CommRingCat.ofHom πk) ≫ z.1 = Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ zero) :
    ∀ b : B, Pl.valuation (g b - algebraMap A (AlgebraicClosure ℚ) (Coalgebra.counit (R := A) b)) < 1 := by sorry
