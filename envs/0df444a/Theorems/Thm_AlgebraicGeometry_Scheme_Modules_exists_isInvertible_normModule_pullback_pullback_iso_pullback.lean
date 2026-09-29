-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_normModule_pullback_pullback_iso_pullback
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isInvertible_normModule_pullback_pullback_iso_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/a3905532-8317-561b-bb64-ff8b5d34e9bb
-- title:
--   Norm of a pullback line bundle is a pullback
-- statement:
--   Let $X$, $Y$, $T$ be schemes and let $\pi : X \to Y$ be a morphism that is finite, flat and locally of finite presentation. Let $d$ be a natural number such that the rank $\pi.\mathrm{finrank}\,y$ equals $d$ at every point $y$ of $Y$, and let $q : Y \to T$ be an arbitrary morphism of schemes. Let $M$ be a module over the structure sheaf of $T$ which is invertible in the sense of `Scheme.Modules.IsInvertible`, i.e. every point of $T$ has an open neighbourhood $U$ such that the restriction of $M$ along the inclusion $U \hookrightarrow T$ is isomorphic to the unit sheaf of modules on $U$. The assertion is that there exists a module $N$ on $T$, again invertible in this local-triviality sense, together with an isomorphism
--   $$\mathrm{normModule}_\pi^d\bigl(\pi^*q^*M\bigr) \;\cong\; q^*N ,$$
--   where $\mathrm{normModule}_\pi^d(L)$ denotes $\det_d(\pi_* L) \otimes \bigl(\det_d(\pi_*\mathbf{1})\bigr)^\vee$, the $d$-th determinant of the pushforward of $L$ tensored with the dual (internal hom into the unit) of the $d$-th determinant of the pushforward of the unit module on $X$. The isomorphism is asserted as the nonemptiness of the type of such isomorphisms, so no particular choice is fixed.
--
--   This is the statement that the norm along a finite flat morphism of constant rank $d$, applied to a line bundle pulled back from a base $T$ through $q$ and then through $\pi$, is itself pulled back from $T$ (concretely by the $d$-th tensor power, though the existential form is what twist-absorbing arguments use). It is used in the relative Picard functor material, in [`AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq`](thm.html#AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_normModule_pullback_pullback_iso_pullback.lean

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

theorem AlgebraicGeometry.Scheme.Modules.exists_isInvertible_normModule_pullback_pullback_iso_pullback
    {X Y T : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d) (q : Y ⟶ T)
    {M : T.Modules} (hM : Scheme.Modules.IsInvertible M) :
    ∃ N : T.Modules, Scheme.Modules.IsInvertible N ∧
      Nonempty (Scheme.Modules.normModule π d ((Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback q).obj M)) ≅
        (Scheme.Modules.pullback q).obj N) := by sorry
