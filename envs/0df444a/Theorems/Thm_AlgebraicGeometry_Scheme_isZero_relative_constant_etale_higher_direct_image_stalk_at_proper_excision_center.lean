-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isZero_relative_constant_etale_higher_direct_image_stalk_at_proper_excision_center
-- name    : AlgebraicGeometry.Scheme.isZero_relative_constant_etale_higher_direct_image_stalk_at_proper_excision_center
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-20T22:07:54.353064+00:00
-- url     : https://prove2.me/theorems/5c429016-de68-48b1-a2ff-fc3cabc4daec
-- title:
--   Vanishing of higher relative direct-image stalks at the center of proper excision
-- statement:
--   Let $f\colon Y\to X$ be proper and an isomorphism on the complement of a closed immersion $i\colon Z\hookrightarrow X$. Write $E=Y\times_X Z$. For a finite abelian group $A$, let $F$ be the kernel of the restriction from the constant sheaf on $Y$ to the direct image of the constant sheaf on $E$. If $s\colon\operatorname{Spec}K\to X$ is a geometric point with separably closed $K$ whose image lies in $Z$, then for each $j>0$,
--   $$(R^j f_*F)_s=0.$$
--   This is the closed-center vanishing needed for the geometric comparison in proper excision.
-- source:
--   Stacks Project, proper base change and extension by zero, https://stacks.math.columbia.edu/tag/095T and https://stacks.math.columbia.edu/tag/095L.

import Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Abelian.RightDerived

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.isZero_relative_constant_etale_higher_direct_image_stalk_at_proper_excision_center
    (A : Type u) [AddCommGroup A] [Finite A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)
    (hs : s default ∈ Set.range i) (q : ℕ) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj
      (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived (q + 1)).obj (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A))) := by sorry
