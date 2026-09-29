-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_eq_of_iso
-- name    : AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_eq_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/d6784567-b5ca-5eea-8301-8355f2c2e21d
-- title:
--   Invariance of the Čech Euler characteristic under isomorphism
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a scheme (both in the bottom universe), let $\pi : V \to \operatorname{Spec} R$ be a morphism of schemes, let $M$ and $M'$ be sheaves of modules on $V$, let $e : M \cong M'$ be an isomorphism between them, and let $\mathcal{K}$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq V$ that are affine and satisfy $\bigsqcup_i U_i = \top$. To $M$ one associates the presheaf of $R$-modules $\mathrm{ofModules}\ \pi\ M$ whose value on an open $U$ is $\Gamma(M,U)$, with $R$-action obtained by restriction of scalars along the structure map $R \to \Gamma(V,U)$ coming from $\pi$ and with restriction maps those of $M$. The conclusion is that the two Euler characteristics agree: $$\sum_{i < |\iota|} (-1)^i \dim_R \check{H}^i(\mathcal{K}, M) = \sum_{i < |\iota|} (-1)^i \dim_R \check{H}^i(\mathcal{K}, M'),$$ where the dimensions are `Module.finrank` of the degree-zero and successive-degree Čech cohomology modules of the respective presheaves for the cover $\mathcal{K}$. No finiteness hypothesis is imposed, `Module.finrank` being $0$ in the non-finite-dimensional case.
--
--   This is the elementary invariance property of the Čech Euler characteristic attached to a fixed ordered affine cover: it depends on the sheaf of modules only up to isomorphism. It is used in the computation of Euler characteristics on abelian schemes, where it feeds into the identity relating the Euler characteristic of a module and of its dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_eq_of_iso.lean

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

theorem AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_eq_of_iso
    {R : Type} [CommRing R] {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of R))
    (M M' : V.Modules) (e : M ≅ M') (𝒦 : V.OrderedAffineCover) :
    (OModulePresheaf.ofModules π M).eulerChar 𝒦 = (OModulePresheaf.ofModules π M').eulerChar 𝒦 := by sorry
