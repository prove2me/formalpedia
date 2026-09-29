-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift
-- name    : AlgebraicGeometry.exists_root_fromNormalization_kummer_existsUnique_lift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/5066ce4d-5e6b-54ee-b485-a078b5652653
-- title:
--   Charts and universal property of the Kummer cover T^k=g
-- statement:
--   Let $R$ be a commutative ring and $X$ an integral scheme equipped with a morphism $f : X \to \operatorname{Spec} R$, all of whose local rings $\mathcal{O}_{X,x}$ are integrally closed. Let $k \in \mathbb{N}$ have invertible image in $R$, let $g \in K(X) =$ `X.functionField` be nonzero, and let $U_0,\dots,U_{r-1}$ be open subsets of $X$ with $\bigsqcup_a U_a = \top$, together with nonzero $h_a \in K(X)$ such that for every $a$ and every $x \in U_a$ both $g/h_a^k$ and $h_a^k/g$ lie in the image of $\mathcal{O}_{X,x}$ in $K(X)$. Put $A' = K(X)[T]/(T^k - g)$ (the `AdjoinRoot` of $X^k - C\,g$), let $f_0$ be $\operatorname{Spec}$ of $K(X) \to A'$ followed by $X$.`fromSpecStalk` at the generic point, and let $\pi : Y \to X$ be the relative normalisation `f₀.fromNormalization` of $f_0$, with $Y =$ `f₀.normalization`. The assertion is the existence of sections $u_a \in \Gamma(U_a, \mathcal{O}_X)$ and $T_a \in \Gamma(\pi^{-1}U_a, \mathcal{O}_Y)$ such that: (i) the germ of $u_a$ at each $x \in U_a$ maps to $g/h_a^k$ in $K(X)$, and each $u_a$ is a unit; (ii) $T_a^k = \pi^{*}u_a$; (iii) for all $a,b$ there is $w \in \Gamma(U_a \cap U_b, \mathcal{O}_X)$ with all germs equal to $h_b/h_a$, satisfying $u_a|_{U_a \cap U_b} = w^k\, u_b|_{U_a \cap U_b}$ and $T_a|_{\pi^{-1}(U_a \cap U_b)} = \pi^{*}(w)\, T_b|_{\pi^{-1}(U_a \cap U_b)}$; and (iv) for every $a$, every scheme $Z$ and morphism $z : Z \to X$ with $z^{-1}(U_a) = \top$, and every $\tau \in \Gamma(Z, \mathcal{O}_Z)$ whose restriction to $z^{-1}(U_a)$ satisfies $\tau^k = z^{*}u_a$, there is a unique $s : Z \to Y$ with $s$ followed by $\pi$ equal to $z$ and $s^{*}T_a = \tau$.
--
--   This is the functor-of-points description of the Kummer covering attached to a $k$-th root of $g$: over each chart $U_a$ the cover is given by the tautological root $T_a = T/h_a$ of the unit $u_a = g/h_a^k$, the charts being compared by $w = h_b/h_a$, and condition (iv) says that $Y$ represents $k$-th roots of $u_a$ over schemes mapping into $U_a$. The chart-by-chart construction rests on the affine case [`AlgebraicGeometry.existsUnique_lift_fromNormalization_kummer_of_isAffineOpen`](thm.html#AlgebraicGeometry.existsUnique_lift_fromNormalization_kummer_of_isAffineOpen), and the result is used in [`AlgebraicGeometry.exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing`](thm.html#AlgebraicGeometry.exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing) to produce sections over closed fibres of henselian local bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.exists_root_fromNormalization_kummer_existsUnique_lift
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : R))
    (g : X.functionField) (hg : g ≠ 0)
    (r : ℕ) (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    let π := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization
    let Y := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).normalization
    ∃ (u : ∀ a, Γ(X, U a)) (T : ∀ a, Γ(Y, π ⁻¹ᵁ (U a))),

      (∀ a (x : X) (hx : x ∈ U a),
        algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (U a) x hx (u a)) = g / h a ^ k) ∧
      (∀ a, IsUnit (u a)) ∧

      (∀ a, T a ^ k = π.app (U a) (u a)) ∧

      (∀ a b, ∃ w : Γ(X, U a ⊓ U b),
        (∀ (x : X) (hx : x ∈ U a ⊓ U b),
          algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (U a ⊓ U b) x hx w) = h b / h a) ∧
        X.presheaf.map (homOfLE inf_le_left).op (u a) = w ^ k * X.presheaf.map (homOfLE inf_le_right).op (u b) ∧
        Y.presheaf.map (homOfLE (π.preimage_mono inf_le_left)).op (T a) =
          π.app (U a ⊓ U b) w * Y.presheaf.map (homOfLE (π.preimage_mono inf_le_right)).op (T b)) ∧

      (∀ a (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ (U a) = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app (U a) (u a) →
          ∃! s : Z ⟶ Y, s ≫ π = z ∧ s.app (π ⁻¹ᵁ (U a)) (T a) = Z.presheaf.map (homOfLE le_top).op τ) := by sorry
