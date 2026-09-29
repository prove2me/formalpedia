-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/e73ed748-5877-5ccb-9ced-2cc511901a30
-- title:
--   Invertible sheaf with non-zero section of finite stabiliser
-- statement:
--   Let $k$ be an algebraically closed field (a universe-$u$ type with a field structure), let $X$ be a scheme and let $t \colon X \to \operatorname{Spec} k$ be a morphism which is proper, with $X$ integral, and such that the object $\mathrm{Over.mk}\ t$ of the category of schemes over $\operatorname{Spec} k$ carries a group-object structure; assume moreover that $t$ is smooth. Then there exist a sheaf of modules $L$ on $X$, a proof that $L$ is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module $\mathcal O_U$, and a morphism $\theta \colon \mathbf 1 \to L$ from the monoidal unit of $X$-modules (a global section of $L$), such that $\theta \neq 0$ and the following set of $k$-points is finite: the set of those morphisms $x \colon \mathrm{Over.mk}\ (\mathrm{id}_{\operatorname{Spec} k}) \to \mathrm{Over.mk}\ t$ (i.e. sections of $t$) with the property that for every such section $z$ one has $\theta$ pulled back along the underlying morphism of $z$ equal to zero if and only if $\theta$ pulled back along the underlying morphism of the product $z \cdot x$ (formed with the group-object multiplication) is zero. Here the pullback of a section along $F \colon X' \to X$ is the composite of the inverse of the canonical isomorphism identifying the pullback of the unit module with the unit module on $X'$ with the image of the section under the pullback functor.
--
--   This is the first step of Mumford's argument that an abelian variety is projective: on a proper smooth integral group scheme over an algebraically closed field there is an invertible module with a non-zero global section whose vanishing locus on $k$-points has finite set-theoretic stabiliser under translation. It is used by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections) in the construction of polarisations for abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [IsIntegral X] [GrpObj (Over.mk t)] (hsm : Smooth t) :
    ∃ (L : X.Modules) (_ : Scheme.Modules.IsInvertible L) (θ : 𝟙_ X.Modules ⟶ L), θ ≠ 0 ∧
      Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
          Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left θ = 0} := by sorry
