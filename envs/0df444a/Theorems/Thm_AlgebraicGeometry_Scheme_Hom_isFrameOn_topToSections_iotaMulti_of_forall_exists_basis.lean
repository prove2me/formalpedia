-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
-- name    : AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/13ab4c89-438e-5843-830f-ec106333c1a1
-- title:
--   Top wedge of a Kähler basis frames detᵈ
-- statement:
--   Let $A$ be a commutative ring, $X$ a scheme and $f : X \to \operatorname{Spec} A$ a morphism, let $d$ be a natural number and let $U \subseteq X$ be an affine open. Via $f$, each $\Gamma(X,W)$ carries the $A$-algebra structure given by $A \to \Gamma(X,W)$ coming from `f.constToPresheaf` (the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism with $f.\mathrm{appLE}\,\top\,W$), in particular $\Gamma(X,U)$ is an $A$-algebra. The assertion is: for every family $\eta : \mathrm{Fin}\,d \to \Omega_{\Gamma(X,U)/A}$, if for every open $W \le U$ which is affine the module $\Omega_{\Gamma(X,W)/A}$ admits a $\Gamma(X,W)$-basis indexed by $\mathrm{Fin}\,d$ whose $i$-th member is the image of $\eta_i$ under `KaehlerDifferential.map A A Γ(X, U) Γ(X, W)` — where $\Gamma(X,W)$ is viewed as a $\Gamma(X,U)$-algebra through the restriction map and the resulting tower over $A$ is assumed to be a scalar tower — then the section $f.\mathrm{topToSections}\,d\,U$ applied to $\eta_1 \wedge \dots \wedge \eta_d$, a section over $U$ of the $d$-th determinant module $\det^d$ of the sheafified relative Kähler module of $f$, is a frame on $U$ in the sense of `Scheme.Modules.IsFrameOn`: for every open $W \le U$ the map $\Gamma(X,W) \to \Gamma(\det^d, W)$, $g \mapsto g \cdot (\text{restriction of the section to } W)$, is bijective.
--
--   This is the local trivialisation statement for the sheaf of top relative differentials: a wedge of differentials that is a basis over all affine opens inside $U$ produces a nowhere-vanishing generating section of $\det^d \Omega_{X/A}$ over $U$. It feeds the criterion [`AlgebraicGeometry.Scheme.Hom.isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension`](thm.html#AlgebraicGeometry.Scheme.Hom.isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension), where such frames are used to compare top differentials along a pullback square of smooth morphisms of fixed relative dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis.lean

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    ∀ (η : Fin d → Ω[Γ(X, U)⁄A]),
      (∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        letI := f.sectionsAlgebra W
        letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
        ∀ [IsScalarTower A Γ(X, U) Γ(X, W)],
          ∃ b : Module.Basis (Fin d) Γ(X, W) (Ω[Γ(X, W)⁄A]),
            ∀ i, b i = KaehlerDifferential.map A A Γ(X, U) Γ(X, W) (η i)) →
      Scheme.Modules.IsFrameOn (f.topToSections d U (exteriorPower.ιMulti Γ(X, U) d η)) U := by sorry
