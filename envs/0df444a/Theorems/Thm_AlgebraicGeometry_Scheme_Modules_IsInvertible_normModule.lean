-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.normModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/90483528-7bdc-5999-b907-52beae17f588
-- title:
--   Norm of an invertible module along a finite flat morphism
-- statement:
--   Let $X$ and $Y$ be schemes and let $\pi \colon X \to Y$ be a morphism that is finite, flat and locally of finite presentation. Let $d$ be a natural number and assume that the rank $\pi.\mathrm{finrank}\, y$ is equal to $d$ at every point $y$ of $Y$. Let $L$ be an object of $X.\mathrm{Modules}$ which is invertible in the sense of `Scheme.Modules.IsInvertible`, i.e. every point $x \in X$ has an open neighbourhood $U$ such that the pullback of $L$ along the open immersion $U.\iota$ is isomorphic to the unit module of the sheaf of rings of $U$. Then the module `Scheme.Modules.normModule π d L` on $Y$, defined as the tensor product of the $d$-th determinant $\det_d((\pi_*)L)$ with the dual $(\det_d(\pi_* \mathbf{1}_{X.\mathrm{Modules}}))^{\vee} = \underline{\mathrm{Hom}}(\det_d(\pi_*\mathbf{1}_{X.\mathrm{Modules}}), \mathbf{1})$, is again invertible in the same local sense: every point of $Y$ has an open neighbourhood on which its restriction is isomorphic to the unit module.
--
--   This is the basic invertibility property of the norm (push-forward determinant) construction for line bundles along a finite locally free morphism of constant rank. It feeds the treatment of the relative Picard functor used here, being cited by the statements about rigidified line bundles and the representability and compatibility results for relative sub-Picard functors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.RelPicard

universe u

set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.normModule
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (Scheme.Modules.normModule π d L) := by sorry
