-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
-- name    : AlgebraicGeometry.eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/55949e65-023a-5f08-a064-39ca04eed434
-- title:
--   Morphisms agreeing on all jets at a point are equal
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in a fixed universe) with $X$ locally Noetherian, and assume that for every open subscheme $U$ of $X$ whose underlying set is non-empty the inclusion morphism `U.ι : U ⟶ X` satisfies the predicate `IsSchemeTheoreticallyDominant`, i.e. has scheme-theoretically dense image in the sense that its scheme-theoretic kernel ideal vanishes. Let $f, g : X \to Y$ be two morphisms of schemes and let $s : Y \to Z$ be a separated morphism such that $f$ followed by $s$ equals $g$ followed by $s$. Let $x$ be a point of $X$ and suppose that for every natural number $n$ the two composites
--   $$\operatorname{Spec}\bigl(\mathcal{O}_{X,x}/\mathfrak{m}_x^{\,n}\bigr) \longrightarrow \operatorname{Spec}\bigl(\mathcal{O}_{X,x}\bigr) \xrightarrow{\ \mathrm{X.fromSpecStalk}\,x\ } X \xrightarrow{\ f,\,g\ } Y$$
--   agree, the first arrow being the spectrum of the quotient map of the stalk at $x$ by the $n$-th power of its maximal ideal. Then $f = g$.
--
--   This is the global rigidity (scheme-theoretic density) statement: a morphism into a separated $Z$-scheme is determined by its restriction to the infinitesimal neighbourhoods of a single point, provided every non-empty open of the source is scheme-theoretically dense; the source is allowed to be non-reduced, as is needed when points with values in local Artinian algebras are used. It serves the study of partial actions on Jacobians of curves of good reduction, where it yields that a group element acting trivially on all jets at a point acts trivially.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
    {X Y Z : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ U : X.Opens, (U : Set X).Nonempty → IsSchemeTheoreticallyDominant U.ι)
    (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    f = g := by sorry
