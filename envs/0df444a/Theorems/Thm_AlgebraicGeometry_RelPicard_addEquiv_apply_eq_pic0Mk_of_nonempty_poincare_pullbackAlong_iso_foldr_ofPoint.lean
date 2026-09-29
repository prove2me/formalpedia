-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_addEquiv_apply_eq_pic0Mk_of_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint
-- name    : AlgebraicGeometry.RelPicard.addEquiv_apply_eq_pic0Mk_of_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/e5d04a50-d2dd-5b87-8bec-5b32538bc7d5
-- title:
--   Poincaré pullbacks of point twists read divisor classes
-- statement:
--   Let $k$ be an algebraically closed field and $c \colon C \to \operatorname{Spec} k$ a proper, geometrically integral morphism that is smooth of relative dimension $1$; let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec} k \to C$ composing with $c$ to the identity). Let $D$ consist of a scheme with structure morphism `D.toBase` to $\operatorname{Spec} k$ and a zero section, and let `hD` exhibit $D$ as representing the rigidified relative $\mathrm{Pic}^0$ functor cut out by the condition `FibrewiseAlgEquivZero`: it provides a Poincaré rigidified invertible module `hD.poincare` on $C \times_k D$ satisfying that condition, such that every rigidified line bundle on $C \times_k T$ satisfying it is, up to isomorphism of underlying modules, the pullback of the Poincaré bundle along a unique $T$-point of `D.toBase`, and such that pulling back along the zero section gives the unit. Let $F$ be a field extension of $k$ in which every nonzero element has a divisor of its orders, of degree zero, let `Mdl` be a curve model of $F$ over $k$, and let $e$ be an isomorphism of `Mdl.C` with $C$ over $\operatorname{Spec} k$, i.e. $e$ followed by $c$ equals `Mdl.toBase`. Let $pt$ assign to every place $v$ of $F/k$ a section $pt\,v$ of $c$, namely the point of `Mdl.C` corresponding to $v$ under `Mdl.pointEquivPlace` followed by $e$. Let $J$ be an additive commutative group, `ptsI` a bijection of $J$ with the sections of `D.toBase`, and assume the pullback of the Poincaré bundle along `ptsI (a + b)` has underlying module isomorphic to the tensor product of those along `ptsI a` and `ptsI b`. Let $\theta$ be an isomorphism of $J$ with $\mathrm{Pic}^0$ of $F/k$, the quotient of the degree-zero divisors by the principal ones, and assume $\theta$ is pinned: whenever $g \in J$, $x$ is a section of $c$ and the pullback of the Poincaré bundle along `ptsI g` is isomorphic to the dual of the ideal sheaf of the graph of $x$ tensored with the ideal sheaf of the graph of $\varepsilon$, there is a degree-zero divisor equal to $[x] - [\varepsilon]$ (the two places being those attached to $x$ and $\varepsilon$ through $e^{-1}$ and `Mdl.pointEquivPlace`) whose class is $\theta g$. Then for $g \in J$ and a degree-zero divisor $Dv$: if the pullback of the Poincaré bundle along `ptsI g` is isomorphic to the iterated tensor product obtained by folding the support list of $Dv$, contributing for each place $v$ the dual of the $(Dv\,v)^{+}$-th power of the ideal sheaf of the graph of $pt\,v$ tensored with the $(Dv\,v)^{-}$-th power of that ideal sheaf, starting from the unit module, then $\theta g$ is the class of $Dv$.
--
--   This is the Abel–Jacobi dictionary in the form needed downstream: a group isomorphism between the $k$-points of the scheme representing the rigidified $\mathrm{Pic}^0$ cut and the degree-zero divisor classes of the function field, pinned on differences of two points, is shown to compute the class of an arbitrary degree-zero divisor from the corresponding twist of the Poincaré bundle. It is used in the reading of the two-chart model of the modular curve, where a Poincaré pullback presented as an explicit product of point twists must be identified with a divisor class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_addEquiv_apply_eq_pic0Mk_of_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.addEquiv_apply_eq_pic0Mk_of_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c)
    (D : RelativePic0Designation k c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F]
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
    (hpt' : ∀ v, pt v = (Mdl.pointEquivPlace.symm v).1 ≫ e.hom)
    {J : Type*} [AddCommGroup J]
    (ptsI : J ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase)
    (haddI : ∀ a b : J, Nonempty
      ((hD.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hD.poincare.pullbackAlong (ptsI a)).L ⊗ (hD.poincare.pullbackAlong (ptsI b)).L))
    (θ : J ≃+ Pic0 k F)
    (hθpin : ∀ (g : J) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c),
      Nonempty ((hD.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ε.1 ε.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := F),
        (Dv : Divisor k F) =
          Finsupp.single (Mdl.pointEquivPlace ⟨x.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl.pointEquivPlace ⟨ε.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact ε.2⟩) 1 ∧
        θ g = Pic0.mk Dv)
    (g : J) (Dv : Divisor.degZero (K := k) (F := F))
    (hg : Nonempty ((hD.poincare.pullbackAlong (ptsI g)).L ≅
          ((((Dv : Divisor k F)).support.toList).foldr
            (fun v M => ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (((Dv : Divisor k F)) v).toNat).invModule ⊗
              ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (-(((Dv : Divisor k F)) v)).toNat).module ⊗ M)
            (𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules)))) :
    θ g = Pic0.mk Dv := by sorry
