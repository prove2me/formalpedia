-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq
-- name    : AlgebraicGeometry.Scheme.Hom.topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/ed890983-79f4-59b3-98dc-3e958b2c5a3d
-- title:
--   Chart independence of reading a top form at an F-point
-- statement:
--   Let $K$ be a commutative ring, let $X$ be a scheme with a morphism $g \colon X \to \operatorname{Spec} K$, and let $d$ be a natural number. Via $g$ every open $U \subseteq X$ carries the $K$-algebra structure on $\Gamma(X,U)$ obtained by pulling back global functions on $\operatorname{Spec} K$ (the map `g.sectionsAlgebra`), and `g.topDifferentials d` is the $d$-th exterior power, sheafified, of the relative Kähler module of this structure map of presheaves of rings; let $\omega$ be a section of `g.topDifferentials d` over $\top$. Let $F$ be a field equipped with a $K$-algebra structure. Let $U_1,U_2 \subseteq X$ be affine opens, each with an algebra map $\Gamma(X,U_i) \to F$ such that $K \to \Gamma(X,U_i) \to F$ is the given $K$-algebra structure on $F$, and assume the two induced morphisms $\operatorname{Spec} F \to \operatorname{Spec}\Gamma(X,U_i) \to X$ (the latter being `IsAffineOpen.fromSpec`) coincide. Let $\omega_i \in \bigwedge^d_{\Gamma(X,U_i)}\Omega_{\Gamma(X,U_i)/K}$ be elements whose images under `g.topToSections d U_i` are both the restriction of $\omega$ to $U_i$. Then the images of $\omega_1$ and $\omega_2$ under the base-change maps `topFormMap` along $\Gamma(X,U_i) \to F$ over $K \to K$ agree in $\bigwedge^d_F \Omega_{F/K}$.
--
--   This is the well-definedness statement behind evaluating a global top-degree relative differential form at an $F$-valued point of $X$: the value does not depend on the affine chart in which the form is written. It is used in the reading of components of Néron models, specifically in the construction of bases and unit factors comparing two specialisations of a top form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq.lean

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq
    {K : Type u} [CommRing K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (ω : Γ(g.topDifferentials d, ⊤))
    (F : Type u) [Field F] [Algebra K F]
    (U₁ : X.Opens) (hU₁ : IsAffineOpen U₁) [Algebra Γ(X, U₁) F]
    (hKU₁ : letI := g.sectionsAlgebra U₁; IsScalarTower K Γ(X, U₁) F)
    (U₂ : X.Opens) (hU₂ : IsAffineOpen U₂) [Algebra Γ(X, U₂) F]
    (hKU₂ : letI := g.sectionsAlgebra U₂; IsScalarTower K Γ(X, U₂) F)
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) F)) ≫ hU₁.fromSpec =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₂) F)) ≫ hU₂.fromSpec)
    (ω₁ : ⋀[Γ(X, U₁)]^d (g.kaehlerPresheaf.obj (op U₁)))
    (hω₁ : g.topToSections d U₁ ω₁ = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
    (ω₂ : ⋀[Γ(X, U₂)]^d (g.kaehlerPresheaf.obj (op U₂)))
    (hω₂ : g.topToSections d U₂ ω₂ = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    letI := g.sectionsAlgebra U₁; letI := g.sectionsAlgebra U₂
    NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₁) F d ω₁ =
      NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₂) F d ω₂ := by sorry
