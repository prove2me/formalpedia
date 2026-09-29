-- Prove2me | Theorems.Thm_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
-- name    : AlgebraicGeometry.isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/a3cf6cbb-c152-5bbf-b4ba-e0d3d78e4617
-- title:
--   Base change of a self-product is cartesian
-- statement:
--   Let $S$ and $R$ be commutative rings, let $A$ be a scheme, and let $f : A \to \operatorname{Spec} S$ and $\sigma : \operatorname{Spec} R \to \operatorname{Spec} S$ be morphisms of schemes. Write $A_R := A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ for the pullback of $f$ along $\sigma$, with projections $p :=$ `pullback.fst f σ` $: A_R \to A$ and $f_R :=$ `pullback.snd f σ` $: A_R \to \operatorname{Spec} R$, and form the two fibre products $A_R \times_{\operatorname{Spec} R} A_R$ (the pullback of $f_R$ along itself) and $A \times_{\operatorname{Spec} S} A$ (the pullback of $f$ along itself). Let $p \times p : A_R \times_{\operatorname{Spec} R} A_R \to A \times_{\operatorname{Spec} S} A$ be the morphism obtained from the universal property out of the two composites of the projections of $A_R \times_{\operatorname{Spec} R} A_R$ with $p$, these two composites agreeing after composition with $f$ because $f_R$ followed by $\sigma$ equals $p$ followed by $f$ and the two projections agree after composition with $f_R$. The assertion is that the commutative square with top edge $p \times p$, left edge the first projection of $A_R \times_{\operatorname{Spec} R} A_R$ followed by $f_R$, right edge the first projection of $A \times_{\operatorname{Spec} S} A$ followed by $f$, and bottom edge $\sigma$, is cartesian.
--
--   This is the statement that the self-product of a base change is the base change of the self-product: $A_R \times_R A_R$ is the fibre product of $A \times_S A$ and $\operatorname{Spec} R$ over $\operatorname{Spec} S$, the structure morphism of $A \times_S A$ over $\operatorname{Spec} S$ being taken via the first projection. It is used in the treatment of polarisations and the Rosati condition on abelian schemes, where line bundles and their rigidifications on $A \times_S A$ are compared with their base changes along $\sigma$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
    {S R : Type} [CommRing S] [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]))
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ)
      (pullback.fst f f ≫ f) σ := by sorry
