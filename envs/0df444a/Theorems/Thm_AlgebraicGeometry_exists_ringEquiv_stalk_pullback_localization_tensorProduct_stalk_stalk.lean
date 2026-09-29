-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
-- name    : AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/aa25086e-a254-5512-889c-cd9a25ff96c8
-- title:
--   Stalks of a fibre product localise the tensor product
-- statement:
--   Let $R$ be a commutative ring and let $f\colon X \to \operatorname{Spec} R$ and $z\colon Z \to \operatorname{Spec} R$ be morphisms of schemes, and let $p$ be a point of the pullback $Z \times_{\operatorname{Spec} R} X$, with images $\zeta = \mathrm{pr}_Z(p)$ under `pullback.fst z f` and $x = \mathrm{pr}_X(p)$ under `pullback.snd z f`. Assume given $R$-algebra structures on the stalks $\mathcal O_{Z,\zeta}$ and $\mathcal O_{X,x}$, each compatible with the structure morphism in the sense that the canonical morphism $\operatorname{Spec} \mathcal O_{Z,\zeta} \to Z$ (`Z.fromSpecStalk`) followed by $z$ equals $\operatorname{Spec}$ of the structure map $R \to \mathcal O_{Z,\zeta}$, and likewise $\operatorname{Spec} \mathcal O_{X,x} \to X$ followed by $f$ equals $\operatorname{Spec}$ of $R \to \mathcal O_{X,x}$. The conclusion asserts the existence of a prime ideal $\mathfrak Q$ of $\mathcal O_{Z,\zeta} \otimes_R \mathcal O_{X,x}$ together with a ring isomorphism $e \colon \mathcal O_{Z\times_R X,\,p} \xrightarrow{\sim} (\mathcal O_{Z,\zeta} \otimes_R \mathcal O_{X,x})_{\mathfrak Q}$ such that $e$ carries the stalk map of `pullback.fst z f` at $p$ to $s \mapsto s \otimes 1$ and the stalk map of `pullback.snd z f` at $p$ to $t \mapsto 1 \otimes t$, both followed by the localisation map.
--
--   This is the standard description of the points and local rings of a fibre product of schemes: the local ring at a point of $Z \times_{\operatorname{Spec} R} X$ is a localisation of the tensor product of the local rings of the two factors, compatibly with the two projections. It is the form in which the statement is used to compare Kähler differentials on a fibre product with their base change, via [`AlgebraicGeometry.bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback`](thm.html#AlgebraicGeometry.bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback), and in the analysis of formal smoothness of stalks in the Néron model infrastructure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p))))) :
    ∃ (𝔔 : Ideal ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))))
      (_ : 𝔔.IsPrime)
      (e : (pullback z f).presheaf.stalk p ≃+* Localization.AtPrime 𝔔),
      (∀ s : Z.presheaf.stalk ((pullback.fst z f).base p),
        e (((pullback.fst z f).stalkMap p).hom s) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) (s ⊗ₜ[R] (1 : X.presheaf.stalk ((pullback.snd z f).base p)))) ∧
      (∀ t : X.presheaf.stalk ((pullback.snd z f).base p),
        e (((pullback.snd z f).stalkMap p).hom t) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) ((1 : Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗ₜ[R] t)) := by sorry
