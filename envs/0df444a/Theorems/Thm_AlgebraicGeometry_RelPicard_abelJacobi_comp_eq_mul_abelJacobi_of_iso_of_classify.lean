-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_abelJacobi_comp_eq_mul_abelJacobi_of_iso_of_classify
-- name    : AlgebraicGeometry.RelPicard.abelJacobi_comp_eq_mul_abelJacobi_of_iso_of_classify
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/2d50d8ad-910e-59c7-af77-1e10378b7d1e
-- title:
--   Isomorphic pointed curves: Abel–Jacobi maps agree up to translation
-- statement:
--   Let $R$ be a commutative ring and let $c\colon C\to\operatorname{Spec}R$, $c'\colon C'\to\operatorname{Spec}R$ be proper, smooth of relative dimension $1$ and geometrically integral, with sections $\varepsilon,\varepsilon'$ (morphisms $\operatorname{Spec}R\to C$, resp. $\to C'$, splitting $c$, resp. $c'$). Let $e\colon C\cong C'$ be an isomorphism compatible with the structure morphisms in both directions, $e_{\mathrm{hom}}$ followed by $c'$ being $c$ and $e_{\mathrm{inv}}$ followed by $c$ being $c'$. Let $D$, $D'$ be $\mathrm{Pic}^0$ designations for $c$, $c'$ (a scheme with a structure morphism to $\operatorname{Spec}R$ and a zero section), and let $h$, $h'$ witness that they represent the functors of rigidified line bundles on $C\times_R T$, resp. $C'\times_R T$, satisfying `FibrewiseAlgEquivZero`, with Poincaré bundles `h.poincare`, `h'.poincare` and classifying maps `h.classify`, `h'.classify`. Let $aj\colon C\to D.P$ and $aj'\colon C'\to D'.P$ be morphisms over $\operatorname{Spec}R$, normalised by $haj$, $haj'$: for every field $K$, every $t\colon \operatorname{Spec}K\to\operatorname{Spec}R$ and every point $x$ of $C$ (resp. $C'$) over $t$, the Poincaré bundle pulled back along $x$ followed by $aj$ is isomorphic to the dual of the ideal module of the relative effective Cartier divisor of $x$, tensored with the ideal module of the divisor of $t$ followed by $\varepsilon$ (resp. $\varepsilon'$); that is, $\mathcal O(\Delta_x)\otimes\mathcal O(-\varepsilon_t)$. Let $\theta\colon D.P\to D'.P$ be a morphism over $\operatorname{Spec}R$ intertwining the classifying maps in the sense of $h\theta$: whenever $M$ on $C\times_R T$ and $N$ on $C'\times_R T$ are rigidified line bundles with `FibrewiseAlgEquivZero`, $Q$ is an invertible module on $T$, and $N$ is isomorphic to the pullback of $M$ along the map $C'\times_R T\to C\times_R T$ induced by $e_{\mathrm{inv}}$, tensored with the pullback of $Q$ along the second projection, then the classifying map of $M$ followed by $\theta$ equals the classifying map of $N$. The conclusion is that for every field $K$, every $t\colon\operatorname{Spec}K\to\operatorname{Spec}R$ and every point $x$ of $C$ over $t$, in the group of $t$-points of $D'$ for the relative group law induced by $h'$ (the subgroup cut `algEquivZeroGroupCut c' ε'`, which adds closure under tensor products and inverses to the fibrewise condition), the product of $x$ followed by $aj$ followed by $\theta$ with $t$ followed by $\varepsilon$, $e_{\mathrm{hom}}$ and $aj'$ equals $x$ followed by $e_{\mathrm{hom}}$ and $aj'$.
--
--   This is the statement that an isomorphism of pointed curves carries one Abel–Jacobi map to the other up to translation by the class of the image of the base point, here in the relative setting of rigidified Picard functors over a base $\operatorname{Spec}R$ and with the comparison of the two $\mathrm{Pic}^0$ objects supplied by a classify-intertwining morphism $\theta$. It is used in the comparison of points on modular curves through an Igusa-type model, in [`ModularCurve.pts_lift_comp_theta_fst_eq_pts_of_dRModelPackage_of_igusaModel`](thm.html#ModularCurve.pts_lift_comp_theta_fst_eq_pts_of_dRModelPackage_of_igusaModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_abelJacobi_comp_eq_mul_abelJacobi_of_iso_of_classify.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.abelJacobi_comp_eq_mul_abelJacobi_of_iso_of_classify
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    [IsProper c'] [SmoothOfRelativeDimension 1 c'] [GeometricallyIntegral c']
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c')
    (e : C ≅ C') (he : e.hom ≫ c' = c) (he' : e.inv ≫ c = c')
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (aj : SchemeHomOver c D.toBase) (aj' : SchemeHomOver c' D'.toBase)
    (haj : ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (haj' : ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c'),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c' x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t)))).idealModule))
    (θ : SchemeHomOver D.toBase D'.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c' ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c') e.inv he' t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c' t)).obj Q) →
        postComp θ (h.classify t M hM) = h'.classify t N hN)
    (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
        ⟨x.1 ≫ aj.1 ≫ θ.1, by rw [Category.assoc, Category.assoc, θ.2, aj.2, x.2]⟩
        ⟨t ≫ ε.1 ≫ e.hom ≫ aj'.1, by
          rw [Category.assoc, Category.assoc, Category.assoc, aj'.2, he, ε.2, Category.comp_id]⟩ =
      ⟨(x.1 ≫ e.hom) ≫ aj'.1, by rw [Category.assoc, Category.assoc, aj'.2, he, x.2]⟩ := by sorry
