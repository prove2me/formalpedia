-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/8624711b-febf-5813-af1c-52512d430342
-- title:
--   Base change for the norm of an invertible module
-- statement:
--   Let $X, Y, X', Y'$ be schemes and let $\pi \colon X \to Y$ be a morphism that is finite, flat and locally of finite presentation. Let $d$ be a natural number such that $\pi$ has fibre rank $d$ at every point of $Y$, i.e. `\pi.finrank y = d` for all $y \in Y$. Let $g \colon Y' \to Y$, $\pi' \colon X' \to Y'$ and $g' \colon X' \to X$ be morphisms forming a cartesian square, in the sense that `IsPullback g' \pi' \pi g` holds for $g'$ followed by $\pi$ against $\pi'$ followed by $g$. Let $L$ be a module on $X$ which is invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ such that the restriction of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module on $U$. Then the type of isomorphisms $$g^{*}\bigl(\det_d(\pi_{*}L) \otimes \det_d(\pi_{*}\mathcal O_X)^{\vee}\bigr) \;\cong\; \det_d(\pi'_{*}g'^{*}L) \otimes \det_d(\pi'_{*}\mathcal O_{X'})^{\vee}$$ is nonempty, where `normModule \pi d L` denotes the left-hand expression, the dual is the internal hom into the unit module, and the same rank parameter $d$ is used on both sides.
--
--   This is the base-change compatibility of the norm (determinant-of-pushforward) construction for an invertible module along a finite locally free morphism of constant rank. It is used in the construction of the relative Picard functor and its rigidified line bundles, where the norm must be transported along changes of base of the parametrising scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso.lean

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

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso
    {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' π' π g)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((Scheme.Modules.pullback g).obj (Scheme.Modules.normModule π d L) ≅
      Scheme.Modules.normModule π' d ((Scheme.Modules.pullback g').obj L)) := by sorry
