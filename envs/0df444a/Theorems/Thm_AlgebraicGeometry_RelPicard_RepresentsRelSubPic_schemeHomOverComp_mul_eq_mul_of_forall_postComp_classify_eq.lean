-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_mul_eq_mul_of_forall_postComp_classify_eq
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.schemeHomOverComp_mul_eq_mul_of_forall_postComp_classify_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/91b0e64d-2de5-5bc1-a465-4a9a29cd44ec
-- title:
--   Picard transport along a curve automorphism is a homomorphism
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c : C \to \operatorname{Spec} R$ a morphism, and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c$ — in diagrammatic order $\varepsilon$ followed by $c$ — equal to the identity. Let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase} : D.P \to \operatorname{Spec} R$ and a zero section, and let $h$ witness that $D$ represents the functor of rigidified line bundles on $C \times_R T$ (an invertible module with a trivialisation along the rigidifying section) whose geometric fibres over all algebraically closed points of $T$ satisfy the predicate `IsAlgEquivZero`, the condition cut out by `algEquivZeroCut`; `h.classify` denotes the resulting classifying $T$-point. Let $w : C \cong C$ be an isomorphism with both $w.\mathrm{hom}$ and $w.\mathrm{inv}$ commuting with $c$, and let $\theta$ be a morphism $D.P \to D.P$ over $\operatorname{Spec} R$. Assume that $\theta$ transports Picard classes along $w^{-1}$ in the following sense: for every $t : T \to \operatorname{Spec} R$, all rigidified line bundles $P_1, P_2$ on $C \times_R T$ satisfying the fibrewise condition, and every invertible module $Q$ on $T$, if $P_2.L$ is isomorphic to the pullback of $P_1.L$ along $w^{-1} \times \mathrm{id}_T$ tensored with the pullback of $Q$ along the projection $C \times_R T \to T$, then the composite of $h.\mathrm{classify}\,t\,P_1$ followed by $\theta$ equals $h.\mathrm{classify}\,t\,P_2$. The conclusion is that $\theta$ is a homomorphism for the relative group law on $D$ induced by tensor product of rigidified bundles (via `algEquivZeroGroupCut`): for every $s : T \to \operatorname{Spec} R$ and all $T$-points $x, y$ of $D$ over $s$, the product $x \cdot y$ followed by $\theta$ equals the product of $x$ followed by $\theta$ and $y$ followed by $\theta$.
--
--   This is the statement that pullback of line bundles along an automorphism of the curve, read through the representing scheme, respects the relative Picard group law, i.e. that a Picard transport is an endomorphism of the relative group scheme. It is the instance, at the relation '$P_2$ is $(w^{-1})^{*}P_1$ twisted by a line bundle from the base', of the general criterion [`AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_mul_of_classify_rel`](thm.html#AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_mul_of_classify_rel), and is used in the construction of Hecke and diamond endomorphisms on the relative Jacobian of the modular curve $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_mul_eq_mul_of_forall_postComp_classify_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.schemeHomOverComp_mul_eq_mul_of_forall_postComp_classify_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (w : C ≅ C) (hw : w.hom ≫ c = c) (hw' : w.inv ≫ c = c)
    (θ : SchemeHomOver D.toBase D.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (P₁ : RigidifiedLineBundle c ε t) (hP₁ : FibrewiseAlgEquivZero P₁)
        (P₂ : RigidifiedLineBundle c ε t) (hP₂ : FibrewiseAlgEquivZero P₂)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (P₂.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) w.inv hw' t)).obj P₁.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t P₁ hP₁) = h.classify t P₂ hP₂) :
    ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) h).mul s x y) θ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) h).mul s
          (NeronModelInfra.schemeHomOverComp x θ) (NeronModelInfra.schemeHomOverComp y θ) := by sorry
