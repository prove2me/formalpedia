-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange
-- name    : AlgebraicGeometry.RelPicard.nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/c8f42713-0322-5e2c-9414-70bb13d4333c
-- title:
--   Abel–Jacobi normalisation descends to the base-changed Poincaré datum
-- statement:
--   Let $R$ be a commutative ring and $c_X\colon X\to\operatorname{Spec}R$ a separated morphism of schemes with a section $\varepsilon$ (so $\varepsilon$ followed by $c_X$ is the identity). Let $D$ be a relative $\mathrm{Pic}^0$ designation for $c_X$, that is, a scheme with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}R$ and a zero section, and let `hrep` express that $D$ represents the subfunctor of rigidified line bundles on $X\times_R(-)$ cut out by the condition `FibrewiseAlgEquivZero`: it provides a rigidified Poincaré bundle satisfying that condition, universality (every such rigidified bundle on $X\times_R T$ is the pullback of the Poincaré bundle along a unique $T\to D.\mathrm{toBase}$ over $\operatorname{Spec}R$, up to isomorphism of the underlying modules), and triviality along the zero section. Let $L'$ be an $R$-algebra and $k'$ a field which is an $L'$-algebra, compatibly over $R$, with $X_{k'}=X\times_R\operatorname{Spec}k'$ smooth of relative dimension one over $k'$. Assume: `hDL`, that the base-changed designation $D_{L'}=D\times_{\operatorname{Spec}R}\operatorname{Spec}L'$ represents the corresponding cut for $X_{L'}$ with section $\varepsilon_{L'}$; `hPL`, that its Poincaré bundle is isomorphic to the transport along `BaseChange.ofR` of the pullback of the Poincaré bundle of `hrep` along the projection $D_{L'}\to D$; `hrepQ`, the analogous representability over $k'$. Let $aj_{L'}$ be a morphism $X_{L'}\to D_{L'}$ over $\operatorname{Spec}L'$ with the Abel–Jacobi property `hajL`: for every $k'$-point $x$ of $X_{L'}$ over $\operatorname{Spec}L'$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $aj_{L'}$ is isomorphic to the line bundle (inverse ideal module) of the relative effective Cartier divisor cut out by the graph of $x$, tensored with the ideal module of the divisor cut out by $\operatorname{Spec}k'\to\operatorname{Spec}L'$ followed by $\varepsilon_{L'}$. Let $k_L\colon X_{k'}\to X_{L'}$ be a morphism compatible with the projections to $X$ and, via $\operatorname{Spec}k'\to\operatorname{Spec}L'$, with the projections to the bases. Finally let $P$ be a $k'$-point of $X_{k'}$ over $\operatorname{Spec}k'$, let $G$ be a $\operatorname{Spec}R$-morphism $\operatorname{Spec}k'\to D$ equal to $P$ followed by $k_L$, $aj_{L'}$ and the projection $D_{L'}\to D$, let $g$ be a $k'$-point of $D_{k'}$ over $\operatorname{Spec}k'$, and assume `isoΘ`, that the pullback of the Poincaré bundle of `hrep` along $G$ is isomorphic to the pullback along the inverse of the comparison $\mathrm{BaseChange.}\kappa$ of the pullback of the Poincaré bundle of `hrepQ` along $g$. Then the pullback of the Poincaré bundle of `hrepQ` along $g$ is isomorphic to the line bundle of the divisor cut out by $P$ tensored with the ideal module of the divisor cut out by the base-changed section $\varepsilon_{k'}$.
--
--   This transfers the Abel–Jacobi normalisation $\mathcal P|_{aj(x)}\cong\mathcal O(x)\otimes\mathcal O(-\varepsilon)$ from the intermediate base $L'$ to the field $k'$, matching a $k'$-point $P$ of the curve with the point $g$ of the base-changed $\mathrm{Pic}^0$ designation that indexes the divisor class of $P-\varepsilon$. It is used in the identification of points of the modular curve $X_1$ with divisor classes through the Laurent-place reduction of the two-chart model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated cX]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    (L' : Type u) [CommRing L'] [Algebra R L'] (k' : Type u) [Field k'] [Algebra R k'] [Algebra L' k'] [IsScalarTower R L' k']
    [SmoothOfRelativeDimension 1 (baseChange R cX k')]
    (hDL : RepresentsRelSubPic (baseChange R cX L') (sectionBaseChange L' ε)
      (algEquivZeroCut (baseChange R cX L') (sectionBaseChange L' ε)) (D.baseChange L'))
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR cX ε L'
      (hrep.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R L'), pullback.condition⟩)).L))
    (hrepQ : RepresentsRelSubPic (baseChange R cX k') (sectionBaseChange k' ε)
      (algEquivZeroCut (baseChange R cX k') (sectionBaseChange k' ε)) (D.baseChange k'))
    (ajL : SchemeHomOver (baseChange R cX L') (D.baseChange L').toBase)
    (hajL : ∀ (x : SchemeHomOver (specMap L' k') (baseChange R cX L')),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange R cX L') x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange R cX L') (specMap L' k' ≫ (sectionBaseChange L' ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (specMap L' k' ≫ ·) (sectionBaseChange L' ε).2).trans
              (Category.comp_id _)))).idealModule))
    (kL : pullback cX (specMap R k') ⟶ pullback cX (specMap R L'))
    (hkL₁ : kL ≫ pullback.fst _ _ = pullback.fst _ _) (hkL₂ : kL ≫ pullback.snd _ _ = pullback.snd _ _ ≫ specMap L' k')
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (baseChange R cX k'))
    (G : SchemeHomOver (specMap R k') D.toBase) (hG : G.1 = P.1 ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap R L'))
    (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (D.baseChange k').toBase)
    (isoΘ : Nonempty ((hrep.poincare.pullbackAlong G).L ≅
      (Scheme.Modules.pullback (BaseChange.κ cX k' (𝟙 (Spec (CommRingCat.of k')))).inv).obj (hrepQ.poincare.pullbackAlong g).L)) :
    Nonempty ((hrepQ.poincare.pullbackAlong g).L ≅
      (RelEffCartierDiv.ofPoint (baseChange R cX k') P.1 P.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange R cX k') (sectionBaseChange k' ε).1 (sectionBaseChange k' ε).2).idealModule) := by sorry
