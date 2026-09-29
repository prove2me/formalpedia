-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback
-- name    : AlgebraicGeometry.bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/e8f76164-1226-5c2b-b461-a90ae2feaabe
-- title:
--   Base change for Kähler differentials at a stalk of a fibre product
-- statement:
--   Let $R$ be a commutative ring, let $X$ and $Z$ be schemes, and let $f\colon X \to \operatorname{Spec} R$ and $z\colon Z \to \operatorname{Spec} R$ be morphisms. Let $p$ be a point of the pullback $P = Z \times_{\operatorname{Spec} R} X$ in Mathlib's sense, with images $\zeta$ under the first projection and $x$ under the second. Assume $R$-algebra structures on the stalks $\mathcal O_{Z,\zeta}$ and $\mathcal O_{X,x}$ that are compatible with the structure morphisms, in the sense that the canonical morphism $\operatorname{Spec}\mathcal O_{Z,\zeta} \to Z$ followed by $z$ equals $\operatorname{Spec}$ of the structure map $R \to \mathcal O_{Z,\zeta}$ (hypothesis `halgZ`), and likewise for $\mathcal O_{X,x}$, $f$ (hypothesis `halgX`); assume also an $R$-algebra structure on $\mathcal O_{P,p}$. Give $\mathcal O_{P,p}$ the algebra structures over $\mathcal O_{Z,\zeta}$ and over $\mathcal O_{X,x}$ coming from the stalk maps of the two projections, and assume both resulting towers $R \to \mathcal O_{Z,\zeta} \to \mathcal O_{P,p}$ and $R \to \mathcal O_{X,x} \to \mathcal O_{P,p}$ are scalar towers. Then the $\mathcal O_{P,p}$-linear composite $$\mathcal O_{P,p} \otimes_{\mathcal O_{X,x}} \Omega_{\mathcal O_{X,x}/R} \longrightarrow \Omega_{\mathcal O_{P,p}/R} \longrightarrow \Omega_{\mathcal O_{P,p}/\mathcal O_{Z,\zeta}},$$ the base-change map followed by the map changing the base ring from $R$ to $\mathcal O_{Z,\zeta}$, is bijective.
--
--   This is the stalkwise form of the base-change isomorphism $\Omega_{P/Z} \cong \mathrm{pr}_X^{*}\,\Omega_{X/\operatorname{Spec} R}$ for a fibre product $P = Z \times_{\operatorname{Spec} R} X$. It is used in the analysis of orders of differential forms on Néron-model constructions, where it transports a basis of $\Omega_{\mathcal O_{X,x}/R}$ to a basis of $\Omega_{\mathcal O_{P,p}/\mathcal O_{Z,\zeta}}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p)))))
    [Algebra R ((pullback z f).presheaf.stalk p)] :
    letI : Algebra (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.fst z f).stalkMap p).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.snd z f).stalkMap p).hom.toAlgebra
    ∀ [IsScalarTower R (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p)]
      [IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p)],
      Function.Bijective
        ((KaehlerDifferential.map R (Z.presheaf.stalk ((pullback.fst z f).base p))
              ((pullback z f).presheaf.stalk p) ((pullback z f).presheaf.stalk p)).restrictScalars
            ((pullback z f).presheaf.stalk p) ∘ₗ
          KaehlerDifferential.mapBaseChange R (X.presheaf.stalk ((pullback.snd z f).base p))
            ((pullback z f).presheaf.stalk p)) := by sorry
