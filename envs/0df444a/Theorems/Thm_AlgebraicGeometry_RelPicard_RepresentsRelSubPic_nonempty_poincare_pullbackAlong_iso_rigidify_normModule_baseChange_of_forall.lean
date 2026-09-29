-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange_of_forall
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange_of_forall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/01fea1a5-0e19-5891-b754-3d34dfa3fd79
-- title:
--   Norm characterisation of an endomorphism survives base change
-- statement:
--   Let $R$ be a commutative ring, $c : C \to \operatorname{Spec} R$ a morphism of schemes and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c = \mathrm{id}$), let $K$ be a commutative $R$-algebra, and let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} R$ and a zero section. Assume $h$ : $D$ represents, with Poincaré bundle $h.\mathrm{poincare}$, the subfunctor of rigidified line bundles on $C$ cut out by `FibrewiseAlgEquivZero`, and $h'$ : the analogous data for the base changes $c_K = \mathrm{pr}_2 : C \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$, $\varepsilon_K$ and $D_K = D.P \times_{\operatorname{Spec} R} \operatorname{Spec} K$; assume moreover $hP$ : the bundle of $h'.\mathrm{poincare}$ is isomorphic to the $K$-base change (via `BaseChange.ofR`) of the pullback of $h.\mathrm{poincare}$ along the projection $D_K \to D.P$. Let $c' : C' \to \operatorname{Spec} R$ and let $\pi_\alpha, \pi_\beta : C' \to C$ be morphisms over $\operatorname{Spec} R$ with $\pi_\alpha$ finite, flat and locally of finite presentation, and let $d$ be a natural number with $\pi_\alpha.\mathrm{finrank}\, x = d$ for every point $x$ of $C$. Let $\varphi$ be an endomorphism of $D.P$ over $\operatorname{Spec} R$ satisfying $h\varphi$: for every scheme $S$, every $t : S \to \operatorname{Spec} R$ and every $S$-point $a$ of $D.P$ over $t$, the bundle of $h.\mathrm{poincare}$ pulled back along $a$ followed by $\varphi$ is isomorphic to $\mathrm{rigidify}$, with respect to the rigidifying section $\mathrm{rigSection}\,c\,t\,\varepsilon$ and the projection $\mathrm{pr}_2 : C \times_{\operatorname{Spec} R} S \to S$ (that is, tensoring with the pullback along $\mathrm{pr}_2$ of the dual of the restriction along that section), of $\mathrm{normModule}$ in degree $d$ for the base-changed leg $\pi_\alpha \times t$, applied to the pullback along $\pi_\beta \times t$ of the bundle of $h.\mathrm{poincare}$ pulled back along $a$; here $\mathrm{normModule}\,\pi\,d\,L = \det{}_d(\pi_* L) \otimes \det{}_d(\pi_* \mathcal{O})^\vee$. Finally let $\varphi_K$ be an endomorphism of $D_K$ over $\operatorname{Spec} K$ with $\varphi_K$ followed by the projection to $D.P$ equal to the projection followed by $\varphi$, and let $\pi_{\alpha,K}, \pi_{\beta,K} : C' \times_{\operatorname{Spec} R}\operatorname{Spec} K \to C \times_{\operatorname{Spec} R}\operatorname{Spec} K$ be morphisms commuting with the projections to $C$ via $\pi_\alpha$, resp. $\pi_\beta$, and with the projections to $\operatorname{Spec} K$. The conclusion is the same identity over $K$: for every scheme $S$, every $t : S \to \operatorname{Spec} K$ and every $S$-point $a$ of $D_K$ over $t$, the bundle of $h'.\mathrm{poincare}$ pulled back along $a$ followed by $\varphi_K$ is isomorphic to the rigidification, with respect to $\mathrm{rigSection}\,c_K\,t\,\varepsilon_K$ and $\mathrm{pr}_2 : C_K \times_{\operatorname{Spec} K} S \to S$, of $\mathrm{normModule}$ in degree $d$ for the $t$-base change of $\pi_{\alpha,K}$ applied to the pullback along the $t$-base change of $\pi_{\beta,K}$ of the bundle of $h'.\mathrm{poincare}$ pulled back along $a$.
--
--   This transports, from the base ring $R$ to an arbitrary commutative $R$-algebra $K$, the characterisation of an endomorphism of the representing object of the relative $\mathrm{Pic}^0$ functor as the correspondence-norm attached to a pair of legs $\pi_\alpha, \pi_\beta : C' \to C$, with $\pi_\alpha$ finite flat of constant rank $d$; no hypothesis that $\operatorname{Spec} K \to \operatorname{Spec} R$ be a monomorphism is imposed, so geometric points are allowed. It is used in the construction of a descent of a Hecke-type generator on the modular curve $X_1(p)$, where the norm identity must be known after base change to the fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange_of_forall.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange_of_forall
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (K : Type u) [CommRing K] [Algebra R K]
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (baseChange R c K) (sectionBaseChange K ε)
      (algEquivZeroCut (baseChange R c K) (sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))

    {C' : Scheme.{u}} {c' : C' ⟶ Spec (CommRingCat.of R)} (πα πβ : SchemeHomOver c' c)
    [IsFinite πα.1] [Flat πα.1] [LocallyOfFinitePresentation πα.1] (d : ℕ) (hd : ∀ x : C, πα.1.finrank x = d)

    (φ : SchemeHomOver D.toBase D.toBase)
    (hφ : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a φ)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange πα.1 πα.2 t) d
            ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 t)).obj (h.poincare.pullbackAlong a).L))))

    (φK : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase)
    (hφK : φK.1 ≫ pullback.fst D.toBase (specMap R K) = pullback.fst D.toBase (specMap R K) ≫ φ.1)

    (παK πβK : pullback c' (specMap R K) ⟶ pullback c (specMap R K))
    (hαK₁ : παK ≫ pullback.fst c (specMap R K) = pullback.fst c' (specMap R K) ≫ πα.1)
    (hαK₂ : παK ≫ pullback.snd c (specMap R K) = pullback.snd c' (specMap R K))
    (hβK₁ : πβK ≫ pullback.fst c (specMap R K) = pullback.fst c' (specMap R K) ≫ πβ.1)
    (hβK₂ : πβK ≫ pullback.snd c (specMap R K) = pullback.snd c' (specMap R K)) :
    ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t (D.baseChange K).toBase),
      Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a φK)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange R c K) t (sectionBaseChange K ε)) (pullback.snd (baseChange R c K) t)
          (Scheme.Modules.normModule
            (curveChange (c := baseChange R c K) (c' := pullback.snd c' (specMap R K)) παK hαK₂ t) d
            ((Scheme.Modules.pullback
                (curveChange (c := baseChange R c K) (c' := pullback.snd c' (specMap R K)) πβK hβK₂ t)).obj
              (h'.poincare.pullbackAlong a).L))) := by sorry
