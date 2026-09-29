-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_pullback_eq_of_iso_over
-- name    : AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_pullback_eq_of_iso_over
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/2be0d81b-ba94-5cdd-b185-be2e5b98a14d
-- title:
--   Euler characteristic invariance under automorphisms over the base field
-- statement:
--   Let $K$ be a field and let $\pi : X \to \operatorname{Spec} K$ be a proper morphism of schemes (over the zeroth universe), let $\sigma : X \cong X$ be an isomorphism of schemes satisfying $\sigma \circ \pi$-compatibility in the form $\sigma_{\mathrm{hom}} \gg \pi = \pi$, i.e. an automorphism of $X$ over $\operatorname{Spec} K$, and let $N$ be a sheaf of modules on $X$ which is invertible in the project's sense: every point of $X$ has an open neighbourhood $U$ such that the restriction of $N$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $\mathcal K$ and $\mathcal K'$ be two ordered affine covers of $X$, each consisting of a finite linearly ordered family of affine open subsets whose supremum is $\top$. For an $\mathcal O$-module presheaf over $\pi$, the quantity `eulerChar` is the alternating sum $\sum_{i<\#\mathcal K_\iota} (-1)^i \dim_K$ of the $K$-dimensions of the associated Čech cohomology modules, the $K$-structure on sections coming from $\pi$. The conclusion is that the Euler characteristic of the presheaf of sections of the pullback $\sigma^{*}N$ computed with respect to $\mathcal K'$ equals the Euler characteristic of the presheaf of sections of $N$ computed with respect to $\mathcal K$.
--
--   This is the invariance of $\chi(X,\mathcal N)$ for an invertible sheaf on a proper scheme over a field under pull-back by an automorphism over the base, together with independence of the chosen finite ordered affine cover. It is used in the computation of Euler characteristics attached to line bundles on abelian schemes, where $\chi(\mathcal L)\chi(\mathcal L^{\vee})$ is compared with a power of $(-1)$ times a rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_pullback_eq_of_iso_over.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_pullback_eq_of_iso_over
    (K : Type) [Field K] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of K)) [IsProper π]
    (σ : X ≅ X) (hσ : σ.hom ≫ π = π) (N : X.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 𝒦' : X.OrderedAffineCover) :
    (OModulePresheaf.ofModules π ((Scheme.Modules.pullback σ.hom).obj N)).eulerChar 𝒦' =
      (OModulePresheaf.ofModules π N).eulerChar 𝒦 := by sorry
