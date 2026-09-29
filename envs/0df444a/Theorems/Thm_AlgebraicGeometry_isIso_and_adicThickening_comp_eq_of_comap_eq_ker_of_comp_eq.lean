-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq
-- name    : AlgebraicGeometry.isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/98605442-1fa3-525d-8af6-9c264333555a
-- title:
--   Traces on adic thickenings of a closed subscheme cut out by graphs
-- statement:
--   Let $R$ be a commutative ring, $I\subseteq R$ an ideal, and let $f:X\to\operatorname{Spec}R$, $g:Y\to\operatorname{Spec}R$ be morphisms of schemes. Write $P=X\times_{\operatorname{Spec}R}Y$ with first projection $\mathrm{pr}_1=$ `pullback.fst f g`, and for a morphism $h$ to $\operatorname{Spec}R$ let the $n$-th adic thickening of $h$ be the pullback of $h$ along $\operatorname{Spec}(R/I^{n+1})\to\operatorname{Spec}R$, with `adicThickeningι` its projection to the source of $h$ and `adicThickeningToBase` its projection to $\operatorname{Spec}(R/I^{n+1})$. Let $J$ be a quasi-coherent ideal sheaf datum on $P$, with associated closed immersion `J.subschemeι` from $Z=V(J)$. Assume given, for every $n$, a morphism $\gamma_n$ from the $n$-th thickening of $f$ to the $n$-th thickening of $\mathrm{pr}_1\circ f$ such that $\gamma_n$ is a closed immersion, the comap of $J$ along $P_n\to P$ equals the kernel ideal sheaf of $\gamma_n$, and $\gamma_n$ followed by $P_n\to P$ followed by $\mathrm{pr}_1$ equals $X_n\to X$. Fix $n$ and a morphism $\zeta$ from the $n$-th thickening of $Z\hookrightarrow P\xrightarrow{\mathrm{pr}_1}X\to\operatorname{Spec}R$ to the $n$-th thickening of $f$ whose composite with $X_n\to X$ is $Z_n\to Z\hookrightarrow P\xrightarrow{\mathrm{pr}_1}X$. Then $\zeta$ is an isomorphism, and the composite $Z_n\to Z\hookrightarrow P$ equals $\zeta$ followed by $\gamma_n$ followed by $P_n\to P$.
--
--   This is the scheme-theoretic bookkeeping step saying that if the trace of a closed subscheme $Z\subseteq X\times_R Y$ on each adic thickening $P_n$ of $X\times_R Y$ is exactly the image of a closed immersion $\gamma_n$ that is a section over $X$, then each thickening $Z_n$ of $Z$ is carried isomorphically onto the corresponding thickening $X_n$ of $X$, compatibly with the immersions into $P$. It is used in the construction of the unique morphism over an adically complete base, [`AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj`](thm.html#AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj); no hypothesis on $R$ or properness enters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (J : (pullback f g).IdealSheafData)
    (γ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening (pullback.fst f g ≫ f) I n)
    (hγ : ∀ n : ℕ, IsClosedImmersion (γ n))
    (hγJ : ∀ n : ℕ, J.comap (adicThickeningι (pullback.fst f g ≫ f) I n) = (γ n).ker)
    (hγX : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g = adicThickeningι f I n)
    (n : ℕ)
    (ζ : adicThickening (J.subschemeι ≫ pullback.fst f g ≫ f) I n ⟶ adicThickening f I n)
    (hζ : ζ ≫ adicThickeningι f I n = adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g) :
    IsIso ζ ∧ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι =
      ζ ≫ γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n := by sorry
