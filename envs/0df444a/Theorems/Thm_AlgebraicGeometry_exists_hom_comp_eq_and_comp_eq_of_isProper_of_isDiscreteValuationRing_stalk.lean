-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk
-- name    : AlgebraicGeometry.exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/19443a58-bee5-59ec-b7c5-c143d2204233
-- title:
--   Extension of morphisms to a proper κ-scheme across DVR points
-- statement:
--   Let $\kappa$ be a field, and let $X$ and $Y$ be schemes equipped with morphisms $f \colon X \to \operatorname{Spec} \kappa$ and $g \colon Y \to \operatorname{Spec} \kappa$, where $X$ is reduced and locally Noetherian and $g$ is proper. Let $U$ be an open subset of $X$, regarded as an open subscheme with canonical immersion `U.ι`, and let $\varphi \colon U \to Y$ be a morphism compatible with the structure morphisms over $\kappa$, that is, $\varphi$ followed by $g$ equals `U.ι` followed by $f$. Assume that every point $x$ of $X$ not lying in $U$ satisfies two conditions: first, the stalk $\mathcal{O}_{X,x}$ is an integral domain and a discrete valuation ring; second, there is a point $y \in U$ with $y \rightsquigarrow x$, i.e. $x$ lies in the closure of $\{y\}$, so that $x$ is a specialisation of a point of $U$. Then $\varphi$ extends to all of $X$ over $\kappa$: there exists a morphism $\tau \colon X \to Y$ such that $\tau$ followed by $g$ equals $f$, and `U.ι` followed by $\tau$ equals $\varphi$.
--
--   This is the scheme-theoretic form of the classical statement that a rational map from a curve to a complete variety is defined at every nonsingular point, here allowed a reducible, merely reduced and locally Noetherian source rather than an integral one; the reduction to the integral case is made through [`AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk`](thm.html#AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk). It is used for extension of morphisms from open subschemes of smooth relative-dimension-one $\kappa$-schemes and, in that form, for morphisms out of charts of the modular curve $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

theorem AlgebraicGeometry.exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk
    {κ : Type u} [Field κ] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of κ)) [IsReduced X] [IsLocallyNoetherian X]
    (g : Y ⟶ Spec (CommRingCat.of κ)) [IsProper g]
    (U : X.Opens) (φ : (U : Scheme.{u}) ⟶ Y) (hφ : φ ≫ g = U.ι ≫ f)
    (hval : ∀ x : X, x ∉ U →
      (∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x)) ∧
        ∃ y : X, y ∈ U ∧ y ⤳ x) :
    ∃ τ : X ⟶ Y, τ ≫ g = f ∧ U.ι ≫ τ = φ := by sorry
