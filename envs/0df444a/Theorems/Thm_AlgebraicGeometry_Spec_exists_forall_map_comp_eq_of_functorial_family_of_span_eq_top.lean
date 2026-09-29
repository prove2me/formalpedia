-- Prove2me | Theorems.Thm_AlgebraicGeometry_Spec_exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top
-- name    : AlgebraicGeometry.Spec.exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/cd971c93-3026-5713-9fe0-cea5f5f19dfc
-- title:
--   Gluing a functorial family of Y-valued points over Spec S
-- statement:
--   Let $S$ be a commutative ring and $Y$ a scheme. Let $\mathrm{adm}$ be a predicate assigning to each commutative ring $S'$ and each ring homomorphism $\psi : S \to S'$ a proposition, assumed stable under post-composition: if $\mathrm{adm}\,\psi$ holds for $\psi : S \to S'$ and $\chi : S' \to S''$ is any ring homomorphism, then $\mathrm{adm}\,(\chi \circ \psi)$ holds. Suppose given, for every admissible $\psi : S \to S'$, a morphism of schemes $z_\psi : \operatorname{Spec} S' \to Y$, and suppose this family is functorial in the sense that for admissible $\psi : S \to S'$ and any $\chi : S' \to S''$ with $\chi \circ \psi$ admissible one has $z_{\chi \circ \psi} = z_\psi \circ \operatorname{Spec}(\chi)$. Let $R \subseteq S$ be a set of elements generating the unit ideal, $\operatorname{span} R = \top$, and assume that for each $r \in R$ the localisation map $S \to S[1/r]$ (the away localisation `Localization.Away r`) is admissible. Then there is a morphism $q : \operatorname{Spec} S \to Y$ such that $q \circ \operatorname{Spec}(\psi) = z_\psi$ for every admissible $\psi : S \to S'$, and such that any morphism $q' : \operatorname{Spec} S \to Y$ satisfying $q' \circ \operatorname{Spec}(S \to S[1/r]) = z_{S \to S[1/r]}$ for all $r \in R$ equals $q$. Thus uniqueness is asserted under the weaker hypothesis that $q'$ agree with the given family only on the distinguished charts indexed by $R$.
--
--   This is the Zariski-sheaf property of the functor of points of a scheme, in the form needed to produce a morphism out of an affine scheme from a family of charts: a functorial family of $Y$-valued points along a class of ring maps containing a distinguished affine cover glues uniquely. It is used in the Čerednik–Drinfel'd part of the development, where morphisms to a scheme $Y$ are constructed chart by chart and then identified by their restrictions to affine charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Spec_exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Spec.exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top
    {S : Type} [CommRing S] {Y : Scheme.{0}}

    (adm : ∀ (S' : Type) [CommRing S'], (S →+* S') → Prop)
    (hadm : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S →+* S') (χ : S' →+* S''),
      adm S' ψ → adm S'' (χ.comp ψ))

    (z : ∀ (S' : Type) [CommRing S'] (ψ : S →+* S'), adm S' ψ → (Spec (CommRingCat.of S') ⟶ Y))
    (hz : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S →+* S') (hψ : adm S' ψ) (χ : S' →+* S'')
      (hχ : adm S'' (χ.comp ψ)), z S'' (χ.comp ψ) hχ = Spec.map (CommRingCat.ofHom χ) ≫ z S' ψ hψ)

    (R : Set S) (hR : Ideal.span R = ⊤)
    (hcov : ∀ r ∈ R, adm (Localization.Away r) (algebraMap S (Localization.Away r))) :
    ∃ q : Spec (CommRingCat.of S) ⟶ Y,
      (∀ (S' : Type) [CommRing S'] (ψ : S →+* S') (hψ : adm S' ψ), Spec.map (CommRingCat.ofHom ψ) ≫ q = z S' ψ hψ) ∧
      ∀ q' : Spec (CommRingCat.of S) ⟶ Y,
        (∀ r (hr : r ∈ R), Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))) ≫ q' =
          z (Localization.Away r) (algebraMap S (Localization.Away r)) (hcov r hr)) → q' = q := by sorry
