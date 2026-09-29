-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_map_topToSections_eq_topToSections_topFormMap
-- name    : AlgebraicGeometry.Scheme.Hom.map_topToSections_eq_topToSections_topFormMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/42a9771e-7d5e-57b4-83dc-8c7f866b7d08
-- title:
--   Naturality of `topToSections` under restriction of opens
-- statement:
--   Let $A$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} A$ a morphism, $d$ a natural number, and $W \le U$ two opens of $X$. The rings $\Gamma(X,U)$ and $\Gamma(X,W)$ are regarded as $A$-algebras through `sectionsAlgebra`, i.e. through the maps obtained from $f$ by composing the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism with $f$'s induced map $A \to \Gamma(X,\cdot)$, and $\Gamma(X,W)$ is regarded as a $\Gamma(X,U)$-algebra through the restriction map `X.presheaf.map (homOfLE hWU).op`; it is assumed that these three structures form a scalar tower. Under these hypotheses, for every $\eta$ in the $d$-th exterior power over $\Gamma(X,U)$ of the value at $U$ of the Kähler presheaf of $f$ (the relative differentials $\Omega_{\Gamma(X,U)/A}$ of the presheaf-of-modules construction applied to `constToPresheaf`), the restriction from $U$ to $W$ of the section `f.topToSections d U η` of the sheaf $\omega^d = \det_d$ of the sheafified Kähler module equals `f.topToSections d W` applied to `topFormMap A A Γ(X, U) Γ(X, W) d η`, the $\Gamma(X,U)$-linear map $\bigwedge^d_{\Gamma(X,U)} \Omega_{\Gamma(X,U)/A} \to \bigwedge^d_{\Gamma(X,W)} \Omega_{\Gamma(X,W)/A}$ induced by functoriality of Kähler differentials along the restriction.
--
--   This is the compatibility of the comparison map from exterior powers of presheaf-level Kähler differentials to sections of the sheaf of top differential forms with restriction to a smaller open, i.e. naturality of `topToSections` in the open set. It is used in the comparison of top forms across affine charts, in particular by [`AlgebraicGeometry.Scheme.Hom.topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq`](thm.html#AlgebraicGeometry.Scheme.Hom.topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_map_topToSections_eq_topToSections_topFormMap.lean

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

theorem AlgebraicGeometry.Scheme.Hom.map_topToSections_eq_topToSections_topFormMap
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U W : X.Opens} (hWU : W ≤ U) :
    letI := f.sectionsAlgebra U; letI := f.sectionsAlgebra W
    letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    ∀ [IsScalarTower A Γ(X, U) Γ(X, W)] (η : ⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U))),
      (f.topDifferentials d).presheaf.map (homOfLE hWU).op (f.topToSections d U η) =
        f.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A A Γ(X, U) Γ(X, W) d η) := by sorry
