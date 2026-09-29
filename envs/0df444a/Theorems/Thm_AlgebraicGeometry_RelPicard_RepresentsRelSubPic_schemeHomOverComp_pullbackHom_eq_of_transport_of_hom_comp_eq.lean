-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/5b153517-18e1-5260-822b-b50f476850a9
-- title:
--   Pull-back commutes with Picard transport along compatible automorphisms
-- statement:
--   Let $R$ be a commutative ring and let $c\colon C\to\operatorname{Spec}R$, $c'\colon C'\to\operatorname{Spec}R$ be schemes over $\operatorname{Spec}R$, each equipped with a section ($\varepsilon$ with $\varepsilon\circ$-composite $c$ equal to the identity, and likewise $\varepsilon'$). Let $D$, $D'$ be relative $\mathrm{Pic}^0$ designations for $c$, $c'$, that is, schemes $D.P$, $D'.P$ over $\operatorname{Spec}R$ with a section of their structure morphism, and let $h$, $h'$ witness that $D$ and $D'$ represent the subfunctors of the rigidified Picard functors of $(c,\varepsilon)$ and $(c',\varepsilon')$ cut out by fibrewise algebraic equivalence to zero: each carries a Poincaré rigidified invertible module satisfying that condition, and every rigidified invertible module on $\mathrm{pullback}\,c\,t$ satisfying it is the pullback of the Poincaré bundle along a unique morphism $t\to D.\mathrm{toBase}$ over $\operatorname{Spec}R$, this morphism being written `classify`. Let $f\colon C'\to C$ satisfy $c\circ f=c'$ and $f\circ\varepsilon'=\varepsilon$, and let $W$ be an automorphism of $C$ and $\alpha$ an automorphism of $C'$ whose `hom` and `inv` parts all commute with the structure morphisms, with $f\circ\alpha=W\circ f$. Let $\theta_W$ be an endomorphism of $D.P$ over $\operatorname{Spec}R$ which is a transport along $W^{-1}$, in the sense that for every $t\colon T\to\operatorname{Spec}R$, all fibrewise algebraically trivial rigidified bundles $M$, $N$ on $\mathrm{pullback}\,c\,t$ and every invertible $Q$ on $T$ with $N.L$ isomorphic to the pullback of $M.L$ along the base change $\mathrm{curveChange}$ of $W^{-1}$ tensored with the pullback of $Q$ along $\mathrm{pullback.snd}\,c\,t$, one has that the classifying morphism of $M$ followed by $\theta_W$ is the classifying morphism of $N$; let $\theta_\alpha$ be such a transport along $\alpha^{-1}$ for $(c',\varepsilon',D')$. Then, for $f^*\colon D.P\to D'.P$ the morphism classifying the $\mathrm{curveChange}$-pullback along $f$ of the Poincaré bundle of $D$, the morphisms $\theta_W$ followed by $f^*$ and $f^*$ followed by $\theta_\alpha$ coincide as morphisms $D.P\to D'.P$ over $\operatorname{Spec}R$.
--
--   This is the functoriality of the relative Picard scheme with respect to automorphisms: a pull-back homomorphism intertwines the transports induced by two automorphisms that are compatible with the pull-back map. It is used in the descent of the diamond operators on the model of $X_1(p)$, where the transports attached to the restrictions of an automorphism to the components of a special fibre must be compared along pull-back.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
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

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
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
    postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') θW =
      postComp θα (RepresentsRelSubPic.pullbackHom f hf hε h h') := by sorry
