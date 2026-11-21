-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_geometric_stalk_equiv_fiber_cohomology_of_proper_excision
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_geometric_stalk_equiv_fiber_cohomology_of_proper_excision
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-20T20:36:59.505347+00:00
-- url     : https://prove2.me/theorems/c85b852c-1fde-4e1e-b201-27f578803278
-- title:
--   Geometric proper base change for relative constants under excision
-- statement:
--   Let $f\colon Y\to X$ be a proper morphism that is an isomorphism over the complement of a closed immersion $i\colon Z\to X$. Write $E=Y\times_X Z$ and let $A$ be a finite abelian group. Let $F$ be the kernel of restriction from the constant sheaf with value $A$ on $Y$ to its closed direct image from $E$. Given a geometric point $s\colon\operatorname{Spec}K\to X$ with $K$ separably closed, let $Y_s=\operatorname{Spec}K\times_X Y$ and denote the projection to $Y$ by $p$. Then for every $j>0$ there is an isomorphism of abelian groups
--   $$ (R^j f_*F)_s\simeq H^j_{\mathrm{et}}(Y_s,p^{-1}F). $$
--   This is the geometric-stalk form of proper base change for the relative coefficients used in the excision square. The inverse image on the fiber is specified by its adjunction.
-- source:
--   Stacks Project, Theorem 59.91.11, https://stacks.math.columbia.edu/tag/095T.

import Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Abelian.RightDerived

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_geometric_stalk_equiv_fiber_cohomology_of_proper_excision
    (A : Type u) [AddCommGroup A] [Finite A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)
    (L : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf (pullback s f).smallEtaleTopology AddCommGrpCat.{u})
    (adj : L ⊣ PhilipponEtaleClosedPushforward.pushforward (pullback.snd s f)) (q : ℕ) :
    Nonempty ((Scheme.pointSmallEtale s).sheafFiber.obj
      (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived (q + 1)).obj (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A)) ≅
      AddCommGrpCat.of ((L.obj (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A)).H (q + 1))) := by sorry
