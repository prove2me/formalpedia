-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_rigidified_cube_pullback_of_isPullback
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_rigidified_cube_pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/e424a00d-6892-5d5e-96cb-17bb7a772ed4
-- title:
--   Rigidified cube bundle pulls back along a cartesian base change
-- statement:
--   Let $S_1$ and $S$ be commutative rings and $\varphi\colon S_1\to S$ a ring homomorphism. Let $f_1\colon A_1\to\operatorname{Spec}S_1$ and $f\colon A\to\operatorname{Spec}S$ be schemes over the respective bases, each equipped with a relative group law ($L_1$, resp. $L$): a functorial group structure on the sets of $T$-points over the base, compatible with base change in $T$. Let $a\colon A\to A_1$ be a morphism making the square $(a,f,f_1,\operatorname{Spec}\varphi)$ cartesian, and assume $a$ is multiplicative: for every scheme $T$, every $t\colon T\to\operatorname{Spec}S$ and all $T$-points $P,Q$ of $f$ over $t$, composing $L.\mathrm{mul}\,t\,P\,Q$ with $a$ gives the $L_1$-product over $t\circ\operatorname{Spec}\varphi$ of $P\circ a$ and $Q\circ a$. Let $M_1$ be a rigidified line bundle on the cube $(A_1\times_{S_1}A_1)\times_{S_1}A_1$ for the structure morphism $\mathrm{prodStr}\,f_1\,f_1$, the unit section of the product group law $L_1\times L_1$ and base $f_1$, i.e. a module which is locally isomorphic to the unit sheaf, together with a trivialisation of its restriction along $x\mapsto((e,e),x)$. Then there exists such a rigidified line bundle $M$ on $(A\times_SA)\times_SA$ for $\mathrm{prodStr}\,f\,f$, the unit of $L\times L$ and $f$, whose underlying module is exactly the pull-back of $M_1$'s module along the morphism $(A\times_SA)\times_SA\to(A_1\times_{S_1}A_1)\times_{S_1}A_1$ induced by $a\times a$ and $a$ over $\operatorname{Spec}\varphi$.
--
--   This is the base-change statement for rigidified line bundles on the threefold fibre product occurring in the theorem of the cube: rigidification along the section $((e,e),\mathrm{id})$ is preserved by pull-back along a cartesian, group-law-compatible morphism. It is used in the construction of a model of a cube bundle over a finitely generated (noetherian) subring of the base, where the bundle over the original base must be recognised as a pull-back of the descended one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_rigidified_cube_pullback_of_isPullback.lean

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

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_rigidified_cube_pullback_of_isPullback
    {S₁ : Type} [CommRing S₁] {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ : RelativeGroupLaw S₁ f₁)
    {S : Type} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    (M₁ : RigidifiedLineBundle (prodStr f₁ f₁) ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of S₁)))) f₁) :
    ∃ M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f,
      M.L = (Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj M₁.L := by sorry
