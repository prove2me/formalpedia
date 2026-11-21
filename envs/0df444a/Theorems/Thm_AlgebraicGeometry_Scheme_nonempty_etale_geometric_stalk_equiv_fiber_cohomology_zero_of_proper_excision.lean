-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_geometric_stalk_equiv_fiber_cohomology_zero_of_proper_excision
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_geometric_stalk_equiv_fiber_cohomology_zero_of_proper_excision
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-20T21:39:02.798186+00:00
-- url     : https://prove2.me/theorems/cb5f8f6b-0850-4af3-b921-ee8948b2626e
-- title:
--   Degree-zero geometric base change for relative constants under excision
-- statement:
--   Let $f\colon Y\to X$ be proper and an isomorphism on the complement of a closed immersion $Z\hookrightarrow X$. Let $E=Y\times_X Z$, and let $F$ be the relative constant sheaf on $(Y,E)$ with values in an abelian group $A$. It is the kernel of restriction from the constant sheaf on $Y$ to the direct image of the constant sheaf on $E$. For a geometric point $s\colon\operatorname{Spec}K\to X$ with $K$ separably closed, let $Y_s=\operatorname{Spec}K\times_X Y$ with projection $p$ to $Y$. Then there is an additive isomorphism
--   $$(R^0 f_*F)_s\simeq H^0_{\mathrm{et}}(Y_s,p^{-1}F).$$
--   This is the degree-zero comparison for the relative coefficients of an excision square. The inverse image on the fiber is specified by its adjunction.
-- source:
--   Stacks Project, Lemma 59.91.4, https://stacks.math.columbia.edu/tag/0A3T.

import Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Abelian.RightDerived

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_geometric_stalk_equiv_fiber_cohomology_zero_of_proper_excision
    (A : Type u) [AddCommGroup A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)
    (L : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf (pullback s f).smallEtaleTopology AddCommGrpCat.{u})
    (adj : L ⊣ PhilipponEtaleClosedPushforward.pushforward (pullback.snd s f)) :
    Nonempty ((Scheme.pointSmallEtale s).sheafFiber.obj
      (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived 0).obj (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A)) ≅
      AddCommGrpCat.of ((L.obj (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A)).H 0)) := by sorry
