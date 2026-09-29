-- Prove2me | Theorems.Thm_AlgebraicGeometry_isReduced_pullback_lift_of_forall_iff_exists_torus
-- name    : AlgebraicGeometry.isReduced_pullback_lift_of_forall_iff_exists_torus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/896ff372-9098-54ae-831a-fb58c33a8ef3
-- title:
--   Reducedness of fibres of a homomorphism pair with split-torus kernel
-- statement:
--   Let $\kappa$ be an algebraically closed field and let $sG : G \to \operatorname{Spec}\kappa$, $sB : B \to \operatorname{Spec}\kappa$ be schemes over $\kappa$, equipped with relative group laws `LG`, `LB`: functorial multiplication, unit and inverse operations on the sets of $T$-points over any $t : T \to \operatorname{Spec}\kappa$ (elements of `SchemeHomOver t sG`, i.e. morphisms $T \to G$ whose composite with $sG$ is $t$), satisfying associativity, the unit laws, left inverses, and compatibility with precomposition by morphisms $T' \to T$ over $\kappa$. Assume $sG$ is smooth and $sB$ locally of finite type. Let $\mathrm{abq}_0,\mathrm{abq}_1 : G \to B$ be morphisms over $\kappa$ which are homomorphisms on $T$-points, i.e. composition with $\mathrm{abq}_i$ carries `LG.mul t a b` to `LB.mul t` of the composites, for all $t$ and all $T$-points $a,b$ of $G$. Write $q : G \to B \times_{\operatorname{Spec}\kappa} B$ for the morphism induced by the pair, and assume $q$ is surjective. Assume further that there are $r : \mathbb{N}$ and a morphism $\tau$ over $\kappa$ from the split torus $\operatorname{Spec}(\kappa[\mathbb{Z}^r])$, with structure morphism `torusStr κ r`, to $G$, such that $\tau$ is a closed immersion and, for every $t : T \to \operatorname{Spec}\kappa$ and every $T$-point $a$ of $G$, the composites of $a$ with both $\mathrm{abq}_i$ are the unit $T$-point of $B$ if and only if $a$ factors as $y$ followed by $\tau$ for some $T$-point $y$ of the torus. Finally let $b : \operatorname{Spec}\kappa \to B \times_{\operatorname{Spec}\kappa} B$ satisfy $b$ followed by the first projection and then $sB$ equal to the identity of $\operatorname{Spec}\kappa$. Then the fibre product of $q$ and $b$ is a reduced scheme.
--
--   This is the standard fact that the fibres of a homomorphism of group schemes over an algebraically closed field whose kernel is a torus are, over rational points, either empty or translates of that torus, hence reduced; here the homomorphism is the pair $(\mathrm{abq}_0,\mathrm{abq}_1)$ into $B \times_\kappa B$ and the kernel is presented by a closed immersion of the split torus $\mathbb{G}_m^r$. It is used in the study of the special fibre of the Picard scheme of a Deligne–Rapoport model, via [`ModularCurve.DRModelPackageLevel.isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq`](thm.html#ModularCurve.DRModelPackageLevel.isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isReduced_pullback_lift_of_forall_iff_exists_torus.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.SplitTorus ModularCurve ModularCurve.DRLevel

universe u

theorem AlgebraicGeometry.isReduced_pullback_lift_of_forall_iff_exists_torus
    {κ : Type u} [Field κ] [IsAlgClosed κ]
    {G B : Scheme.{u}} (sG : G ⟶ Spec (CommRingCat.of κ)) (sB : B ⟶ Spec (CommRingCat.of κ))
    (LG : RelativeGroupLaw κ sG) (LB : RelativeGroupLaw κ sB) (hsm : Smooth sG) [LocallyOfFiniteType sB]
    (abq : Fin 2 → SchemeHomOver sG sB)

    (habq : ∀ (i : Fin 2) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a b : SchemeHomOver t sG),
      NeronModelInfra.schemeHomOverComp (LG.mul t a b) (abq i) =
        LB.mul t (NeronModelInfra.schemeHomOverComp a (abq i)) (NeronModelInfra.schemeHomOverComp b (abq i)))

    (hsurj : Surjective (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)))

    (r : ℕ) (τ : SchemeHomOver (torusStr κ r) sG) (hτ : IsClosedImmersion τ.1)
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t sG),
      (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) = LB.one t) ↔
        ∃ y : SchemeHomOver t (torusStr κ r), NeronModelInfra.schemeHomOverComp y τ = a)

    (b : Spec (CommRingCat.of κ) ⟶ pullback sB sB) (hb : b ≫ pullback.fst sB sB ≫ sB = 𝟙 _) :
    IsReduced (pullback (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) b) := by sorry
