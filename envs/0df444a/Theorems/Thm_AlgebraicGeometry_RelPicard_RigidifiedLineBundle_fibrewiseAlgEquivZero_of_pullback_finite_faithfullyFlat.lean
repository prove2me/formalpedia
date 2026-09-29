-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/29ab8622-e814-514f-a677-eb42b828d524
-- title:
--   Fibrewise algebraic triviality descends along finite faithfully flat base change
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a morphism of schemes and $\varepsilon$ an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Let $R'$ be an $R$-algebra which is finite as an $R$-module and faithfully flat over $R$, and let $t\colon T\to\operatorname{Spec}R$ be a further morphism. Let $M$ be a rigidified line bundle for $(c,\varepsilon)$ over $t$: an invertible module $M.L$ on the fibre product $C\times_{\operatorname{Spec}R}T$ (invertible in the sense that every point has a neighbourhood $U$ on which the restriction is isomorphic to the unit module), together with a trivialisation of the pullback of $M.L$ along the section `rigSection c t ε`. Write $T'=T\times_{\operatorname{Spec}R}\operatorname{Spec}R'$, regarded over $\operatorname{Spec}R$ by $\operatorname{pr}_2$ followed by $\operatorname{Spec}(R\to R')$, and let $M'$ be the pullback of $M$ along the first projection $T'\to T$ (so $M'.L$ is the pullback of $M.L$ along the induced morphism $C\times_{\operatorname{Spec}R}T'\to C\times_{\operatorname{Spec}R}T$). Assume `FibrewiseAlgEquivZero M'`, that is: for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to T'$, the pullback of $M'.L$ to the fibre $(C\times_{\operatorname{Spec}R}T')\times_{T'}\operatorname{Spec}k$ over $\operatorname{Spec}k$ satisfies `IsAlgEquivZero`: there exist a scheme $P$ with a locally of finite type, geometrically integral morphism $h\colon P\to\operatorname{Spec}k$, an invertible module on the fibre product of the fibre with $P$, and two sections $t_0,t_1$ of $h$, such that the restriction along $t_0$ is isomorphic to the unit module and the restriction along $t_1$ is isomorphic to the given bundle. The conclusion is the same property `FibrewiseAlgEquivZero` for $M$ itself, over all algebraically closed fields $k$ and all $\operatorname{Spec}k\to T$.
--
--   This is the descent step asserting that the condition "algebraically equivalent to zero on every geometric fibre", which cuts out the subfunctor $\mathrm{Pic}^0$ of the rigidified relative Picard functor, can be tested after a finite faithfully flat base change $R\to R'$. It is used in the verification of the sheaf condition for the relevant subpresheaf with respect to finite faithfully flat covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (h : FibrewiseAlgEquivZero (M.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩)) :
    FibrewiseAlgEquivZero M := by sorry
