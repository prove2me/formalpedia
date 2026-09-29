-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_classifies_rigidify_pullback_map_comp_of_classifies_pullback_curveChange_inv_of_classifies_rigidify_pullback_map
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.classifies_rigidify_pullback_map_comp_of_classifies_pullback_curveChange_inv_of_classifies_rigidify_pullback_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/8156ecb0-99ad-5035-bca7-a3df05ffb260
-- title:
--   Composing semilinear Picard transport with an automorphism transport
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme with a structure morphism $c : C \to \operatorname{Spec} R$ and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c = \mathrm{id}$), and let $D$ consist of a scheme with structure morphism `D.toBase` to $\operatorname{Spec} R$ together with a zero section. Assume $h$ exhibits $D$ as representing the functor of rigidified line bundles on $C \times_R T$ that are fibrewise algebraically equivalent to zero: it provides a Poincaré bundle on $C \times_R D$, a unique classifying morphism `h.classify t M hM` over $\operatorname{Spec} R$ for each such bundle $M$ on $C\times_R T$, and the normalisation at the zero section. Let $e$ be an automorphism of $C$ with $e_{\mathrm{hom}} \circ c = c$ and $e^{-1} \circ c = c$, and let $\theta$ be an endomorphism of $D$ over $\operatorname{Spec} R$ satisfying: for all $t : T \to \operatorname{Spec} R$, all fibrewise algebraically trivial rigidified bundles $M, N$ on $C\times_R T$ and every invertible $Q$ on $T$, if $N.L$ is isomorphic to the pullback of $M.L$ along $e^{-1} \times \mathrm{id}_T$ tensored with the pullback of $Q$ along the projection $C \times_R T \to T$, then $\theta \circ \mathrm{classify}(M) = \mathrm{classify}(N)$. Let $\beta, \beta'$ be mutually inverse automorphisms of $\operatorname{Spec} R$, let $f : C \to C$ satisfy $f \circ c = \beta \circ c$, and let $N$ be a morphism of $D$ to itself with $N \circ \mathrm{toBase} = \beta' \circ \mathrm{toBase}$ such that, for every $t : T \to \operatorname{Spec} R$ and every $T$-point $a$ of $D$ over $t$, the Poincaré bundle pulled back along $a \circ N$ (a point over $\beta' \circ t$) is isomorphic to the rigidification, along the section $\mathrm{rigSection}\,c\,(\beta' \circ t)\,\varepsilon$ and the projection $C \times_R (\beta'\circ t) \to T$, of the pullback along $f \times \mathrm{id}_T$ of the Poincaré bundle pulled back along $a$; here rigidification of $L$ means $L$ tensored with the pullback along the projection of the dual of the restriction of $L$ along the section. The conclusion is the same statement with $N$ replaced by the composite $N$ followed by $\theta$ and with $f$ replaced by $e^{-1}$ followed by $f$.
--
--   This is the composition law for semilinear transports on the representing object of the fibrewise algebraically trivial rigidified relative Picard functor: an automorphism transport $\theta$ may be absorbed into the curve morphism defining the transport. It is used in verifying the compatibilities between Galois actions and diamond operators on the Jacobian of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_classifies_rigidify_pullback_map_comp_of_classifies_pullback_curveChange_inv_of_classifies_rigidify_pullback_map.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian
universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.classifies_rigidify_pullback_map_comp_of_classifies_pullback_curveChange_inv_of_classifies_rigidify_pullback_map
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    (e : C ≅ C) (he : e.hom ≫ c = c) (he' : e.inv ≫ c = c)
    (θ : SchemeHomOver D.toBase D.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) e.inv he' t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t M hM) = h.classify t N hN)

    (β β' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
    (hβ : β' ≫ β = 𝟙 (Spec (CommRingCat.of R))) (hβ' : β ≫ β' = 𝟙 (Spec (CommRingCat.of R)))
    (f : C ⟶ C) (hf : f ≫ c = c ≫ β)
    (N : SchemeHomOver (D.toBase ≫ β') D.toBase)
    (hN :
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h.poincare.pullbackAlong
            (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ β') D.toBase)).L ≅
          Scheme.Modules.rigidify (rigSection c (t ≫ β') ε) (pullback.snd c (t ≫ β'))
            ((Scheme.Modules.pullback
                (pullback.map c (t ≫ β') c t f (𝟙 T) β hf.symm
                  (by rw [Category.assoc, hβ, Category.comp_id, Category.id_comp]))).obj
              (h.poincare.pullbackAlong a).L)))) :

      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h.poincare.pullbackAlong
            (⟨a.1 ≫ (N.1 ≫ θ.1), by rw [Category.assoc, Category.assoc, θ.2, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ β') D.toBase)).L ≅
          Scheme.Modules.rigidify (rigSection c (t ≫ β') ε) (pullback.snd c (t ≫ β'))
            ((Scheme.Modules.pullback
                (pullback.map c (t ≫ β') c t (e.inv ≫ f) (𝟙 T) β (by rw [Category.assoc, hf, ← Category.assoc, he'])
                  (by rw [Category.assoc, hβ, Category.comp_id, Category.id_comp]))).obj
              (h.poincare.pullbackAlong a).L))) := by sorry
