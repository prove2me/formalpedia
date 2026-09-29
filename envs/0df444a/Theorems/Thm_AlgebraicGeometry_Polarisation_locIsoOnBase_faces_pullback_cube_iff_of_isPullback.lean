-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_faces_pullback_cube_iff_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/0a1afb45-de83-5cc5-876d-78c3369677bd
-- title:
--   Cube face triviality transfers along a cartesian base change
-- statement:
--   Let $S_1$ be a commutative ring, $f_1\colon A_1\to\operatorname{Spec}S_1$ a morphism of schemes carrying a relative group law $L_1$ (a functorial multiplication, unit and inverse on sections of $f_1$ over varying bases, satisfying the group axioms and compatible with base change), let $\varphi\colon S_1\to S$ be a ring homomorphism, and let $f\colon A\to\operatorname{Spec}S$ carry a relative group law $L$. Let $a\colon A\to A_1$ be such that the square formed by $a$, $f$, $f_1$ and $\operatorname{Spec}\varphi$ is cartesian, and assume $a$ is multiplicative: for every scheme $T$, every $t\colon T\to\operatorname{Spec}S$ and all sections $P,Q$ of $f$ over $t$, composing $L.\mathrm{mul}\,t\,P\,Q$ with $a$ gives the $L_1$-product over $t$ followed by $\operatorname{Spec}\varphi$ of $P\circ a$ and $Q\circ a$. Let $N$ be a module on $(A_1\times_{S_1}A_1)\times_{S_1}A_1$, the double pullback formed from $\mathrm{prodStr}\,f_1\,f_1=\mathrm{pr}_1\circ f_1$ and $f_1$. Write $a\times a\times a$ for the induced morphism $(A\times_SA)\times_SA\to(A_1\times_{S_1}A_1)\times_{S_1}A_1$, and for each of the three faces $(x,y)\mapsto((e,x),y)$, $((x,e),y)$, $((x,y),e)$, formed with the unit section of the respective group law, consider the pullback of $N$ along $a\times a\times a$ followed by that face. The conclusion is a conjunction of three equivalences, one per face: this module on $A\times_SA$ is isomorphic to the monoidal unit locally over $\operatorname{Spec}S$ (i.e. for every point of $\operatorname{Spec}S$ there is an open neighbourhood $U$ on whose preimage under $\mathrm{prodStr}\,f\,f$ the two are isomorphic) if and only if the corresponding face-pullback of $N$ on $A_1\times_{S_1}A_1$, base changed along the projection to $(A_1\times_{S_1}A_1)\times_{\operatorname{Spec}S_1}\operatorname{Spec}S$, is isomorphic to the unit locally over $\operatorname{Spec}S$ relative to the second projection.
--
--   This is the base-change comparison for the three face restrictions occurring in the theorem of the cube: it identifies local triviality over the base of the faces of a cube module pulled back to $A$ with local triviality of the faces computed on $A_1$ and then base changed. It is used in the construction of Noetherian models of rigidified line bundles, where face triviality must be transported between a ring and a finitely generated subring of it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_faces_pullback_cube_iff_of_isPullback
    {S₁ : Type} [CommRing S₁] {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ : RelativeGroupLaw S₁ f₁)
    {S : Type} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    (N : (pullback (prodStr f₁ f₁) f₁).Modules) :
    (LocIsoOnBase (prodStr f f)
        ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj ((Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))).obj
          ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (L₁.one (prodStr f₁ f₁)).1 (pullback.fst f₁ f₁) (by rw [(L₁.one _).2]))
          (pullback.snd f₁ f₁)
          (by rw [pullback.lift_fst_assoc, (L₁.one _).2]; exact pullback.condition))).obj N)) (𝟙_ _)) ∧
    (LocIsoOnBase (prodStr f f)
        ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj ((Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))).obj
          ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (pullback.fst f₁ f₁) (L₁.one (prodStr f₁ f₁)).1 (by rw [(L₁.one _).2]))
          (pullback.snd f₁ f₁)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj N)) (𝟙_ _)) ∧
    (LocIsoOnBase (prodStr f f)
        ((Scheme.Modules.pullback (pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2]))).obj ((Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))).obj
          ((Scheme.Modules.pullback (pullback.lift (𝟙 _) (L₁.one (prodStr f₁ f₁)).1 (by rw [Category.id_comp, (L₁.one _).2]))).obj N)) (𝟙_ _)) := by sorry
