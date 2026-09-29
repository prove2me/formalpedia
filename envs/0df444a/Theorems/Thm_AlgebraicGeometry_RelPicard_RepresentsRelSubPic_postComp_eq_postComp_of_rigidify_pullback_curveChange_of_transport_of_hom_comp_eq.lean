-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_eq_postComp_of_rigidify_pullback_curveChange_of_transport_of_hom_comp_eq
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_eq_postComp_of_rigidify_pullback_curveChange_of_transport_of_hom_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/706bf027-3bc0-509b-99c9-d361d84953a0
-- title:
--   Compatibility of ν with the Picard transports of W and α
-- statement:
--   Let $R$ be a commutative ring and let $c : C \to \operatorname{Spec} R$, $c' : C' \to \operatorname{Spec} R$ be schemes over $\operatorname{Spec} R$ equipped with sections $\varepsilon$, $\varepsilon'$ (morphisms $\operatorname{Spec} R \to C$, resp. $C'$, composing with $c$, resp. $c'$, to the identity). Let $D$, $D'$ be designations, each consisting of a scheme with a structure morphism `toBase` to $\operatorname{Spec} R$ and a zero section, and let $h$, $h'$ witness that $D$, $D'$ represent the functor of rigidified invertible modules on $\operatorname{pullback} c\, t$, resp. $\operatorname{pullback} c'\, t$, satisfying `FibrewiseAlgEquivZero` (the condition `algEquivZeroCut`: each geometric fibre pull-back is `IsAlgEquivZero`); in particular each carries a Poincaré bundle over $D.\mathrm{toBase}$, resp. $D'.\mathrm{toBase}$, and for every $t : T \to \operatorname{Spec} R$ and every such $M$ there is a unique $T$-point `classify` of the designation whose pull-back of the Poincaré bundle is isomorphic to $M.L$. Let $f : C' \to C$ satisfy $f$ followed by $c$ equal to $c'$. Let $\nu$ be a morphism of the underlying schemes of $D$ into that of $D'$ over $\operatorname{Spec} R$, subject to the hypothesis that for every $t : T \to \operatorname{Spec} R$ and every $T$-point $a$ of $D$ over $\operatorname{Spec} R$, the pull-back of the Poincaré bundle of $D'$ along $a$ followed by $\nu$ is isomorphic to $\mathrm{rigidify}$ with respect to the section $\mathrm{rigSection}\, c'\, t\, \varepsilon'$ and the projection $\mathrm{pullback.snd}\, c'\, t$ — that is, $L \otimes q^{*}(\sigma^{*}L)^{\vee}$ — applied to the pull-back along $\mathrm{curveChange}\, f\, h_f\, t = f \times \mathrm{id}_T$ of the pull-back of the Poincaré bundle of $D$ along $a$. Let $W$ be a self-isomorphism of $C$ with both $W.\mathrm{hom}$ and $W.\mathrm{inv}$ compatible with $c$, let $\alpha$ be a self-isomorphism of $C'$ with both $\alpha.\mathrm{hom}$ and $\alpha.\mathrm{inv}$ compatible with $c'$, and assume $\alpha.\mathrm{hom}$ followed by $f$ equals $f$ followed by $W.\mathrm{hom}$. Let $\theta_W$ be an endomorphism of $D$ over $\operatorname{Spec} R$ which transports $W.\mathrm{inv}$, in the sense that for all $t : T \to \operatorname{Spec} R$, all rigidified bundles $M$, $N$ on $\operatorname{pullback} c\, t$ satisfying `FibrewiseAlgEquivZero`, and every invertible $T$-module $Q$, an isomorphism $N.L \cong (W.\mathrm{inv} \times \mathrm{id}_T)^{*}M.L \otimes (\mathrm{pullback.snd}\, c\, t)^{*}Q$ forces the classifying point of $M$ followed by $\theta_W$ to equal the classifying point of $N$; let $\theta_\alpha$ be an endomorphism of $D'$ transporting $\alpha.\mathrm{inv}$ in the same sense relative to $h'$. The conclusion is the equality of morphisms from the scheme of $D$ to that of $D'$ over $\operatorname{Spec} R$: $\theta_W$ followed by $\nu$ equals $\nu$ followed by $\theta_\alpha$.
--
--   This is a functoriality statement for the relative Picard functor of fibrewise algebraically trivial rigidified line bundles: a morphism $\nu$ pinned by a rigidification identity over $f$ intertwines the transports attached to automorphisms $W$ of $C$ and $\alpha$ of $C'$ that commute with $f$; no compatibility of $\nu$ with the marked sections is assumed. It is used in the descent of diamond operators to the special-fibre components of a model of $X_1(p)$, being cited by [`ModularCurve.XOneP.exists_descent_diamondGen_of_coprime_specialFibre_components_of_abelJacobi_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_descent_diamondGen_of_coprime_specialFibre_components_of_abelJacobi_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_eq_postComp_of_rigidify_pullback_curveChange_of_transport_of_hom_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_eq_postComp_of_rigidify_pullback_curveChange_of_transport_of_hom_comp_eq
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (f : C' ⟶ C) (hf : f ≫ c = c')

    (ν : SchemeHomOver D.toBase D'.toBase)
    (hν : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
          Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L)))
    (W : C ≅ C) (hW : W.hom ≫ c = c) (hW' : W.inv ≫ c = c)
    (α : C' ≅ C') (hα : α.hom ≫ c' = c') (hα' : α.inv ≫ c' = c')
    (hcomm : α.hom ≫ f = f ≫ W.hom)
    (θW : SchemeHomOver D.toBase D.toBase)
    (hθW : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) W.inv hW' t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θW (h.classify t M hM) = h.classify t N hN))
    (θα : SchemeHomOver D'.toBase D'.toBase)
    (hθα : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c' ε' t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c' ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c') (c' := c') α.inv hα' t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c' t)).obj Q) →
        postComp θα (h'.classify t M hM) = h'.classify t N hN)) :
    postComp ν θW = postComp θα ν := by sorry
