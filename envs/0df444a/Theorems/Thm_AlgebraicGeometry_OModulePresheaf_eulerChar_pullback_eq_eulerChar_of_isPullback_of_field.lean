-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_pullback_eq_eulerChar_of_isPullback_of_field
-- name    : AlgebraicGeometry.OModulePresheaf.eulerChar_pullback_eq_eulerChar_of_isPullback_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/cdd1fe47-5048-5047-8b8b-205c87ba11c1
-- title:
--   Field extension invariance of the Čech Euler characteristic
-- statement:
--   Let $K$ and $K'$ be fields, the latter a $K$-algebra, and let $A$, $A'$ be schemes (in the bottom universe). Let $f : A \to \operatorname{Spec} K$ be proper, let $f' : A' \to \operatorname{Spec} K'$, and let $g : A' \to A$ be such that the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $K \to K'$ is cartesian. Let $M$ be a sheaf of modules on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $M$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of modules of $U$. Finally let $\mathcal{K}$ and $\mathcal{K}'$ be ordered affine covers of $A$ and $A'$ respectively, that is, finite linearly ordered families of affine open subsets whose supremum is the whole space. The conclusion equates two integers: the alternating sum $\sum_{i < \#\mathcal{K}'.\iota} (-1)^i \dim_{K'}$ of the Čech cohomology modules (in degree $0$, and the degrees $i+1$) of the presheaf of sections of the pullback $(g)^{*}M$ with respect to $\mathcal{K}'$, regarded over $K'$ via $f'$, and the corresponding alternating sum $\sum_{i < \#\mathcal{K}.\iota} (-1)^i \dim_{K}$ for the presheaf of sections of $M$ with respect to $\mathcal{K}$, regarded over $K$ via $f$.
--
--   This is the invariance of the Čech Euler characteristic $\chi(M)$ of an invertible sheaf on a proper scheme over a field under extension of the base field, together with independence of the chosen finite affine cover; classically it is flat base change for cohomology along $K \to K'$ applied degree by degree. It is used in the treatment of polarised abelian schemes, where $\chi$ of the polarising bundle is compared with the degree of the associated isogeny, and in the comparison of Euler characteristics of isomorphic modules over a base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_pullback_eq_eulerChar_of_isPullback_of_field.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.OModulePresheaf.eulerChar_pullback_eq_eulerChar_of_isPullback_of_field
    (K K' : Type) [Field K] [Field K'] [Algebra K K']
    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [IsProper f] (f' : A' ⟶ Spec (CommRingCat.of K'))
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒦 : A.OrderedAffineCover) (𝒦' : A'.OrderedAffineCover) :
    (OModulePresheaf.ofModules f' ((Scheme.Modules.pullback g).obj M)).eulerChar 𝒦' =
      (OModulePresheaf.ofModules f M).eulerChar 𝒦 := by sorry
