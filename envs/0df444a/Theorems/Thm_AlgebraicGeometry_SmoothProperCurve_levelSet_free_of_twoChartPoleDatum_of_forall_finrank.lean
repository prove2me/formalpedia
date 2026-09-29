-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_levelSet_free_of_twoChartPoleDatum_of_forall_finrank
-- name    : AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum_of_forall_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/141ec2f6-85da-5195-9c5b-6468ebc22407
-- title:
--   Level sets of a two-chart pole datum are free of rank m
-- statement:
--   Let $R$ be a Noetherian commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a proper morphism that is smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity of $\operatorname{Spec}R$. Let $U,V$ be open subsets of $C$, both affine, with $U\sqcup V=\top$, and suppose $U$ is exactly the complement of the image of the underlying map of $\varepsilon$ (a point lies in $U$ iff it is not in that image). Let $f\in\Gamma(C,U)$ and $g\in\Gamma(C,V)$ satisfy $U\cap V=C_f=C_g$ (the basic open sets of $f$ and of $g$) and let the restrictions of $f$ and $g$ to $U\cap V$ have product $1$. Here and below $\Gamma(C,U)$ and $\Gamma(C,V)$ carry the $R$-algebra structures induced by $c$ through the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism followed by $c.appLE$. Let $m\in\mathbb{N}$ and assume: for every field $L$ that is an $R$-algebra, $\dim_L\bigl(L\otimes_R(\Gamma(C,V)/(g))\bigr)=m$; the $R$-algebra map $R[X]\to\Gamma(C,U)$, $X\mapsto f$, is finite; and the $R$-algebra map $R[X]\to\Gamma(C,V)$, $X\mapsto g$, is finite. Then for every local commutative $R$-algebra $S$ and every $s\in S$, the $S$-module $S\otimes_R\Gamma(C,U)/(1\otimes f-s\otimes 1)$ is module-finite over $S$, free over $S$, and of rank $m$.
--
--   This is the fibrewise freeness statement for the chart $U=C\setminus\varepsilon$ of a two-chart pole datum on a proper smooth relative curve: the level sets of the coordinate $f$, viewed as fibres of $\Gamma(C,U)$ over the affine line, are finite free of constant rank $m$ over an arbitrary local $R$-algebra, the base $R$ being only Noetherian rather than local. It is used to produce a finite map datum of exact degree $m$ over a general Noetherian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_levelSet_free_of_twoChartPoleDatum_of_forall_finrank.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum_of_forall_finrank
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (m : ℕ)
    (hrank : ∀ (L : Type u) [Field L] [Algebra R L],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.finrank L (L ⊗[R] (Γ(C, V) ⧸ Ideal.span {g})) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite) :
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
      Module.Finite S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
        Module.Free S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
        Module.finrank S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m := by sorry
