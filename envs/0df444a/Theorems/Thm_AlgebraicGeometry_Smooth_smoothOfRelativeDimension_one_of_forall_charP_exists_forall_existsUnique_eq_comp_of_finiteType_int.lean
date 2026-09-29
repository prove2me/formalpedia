-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int
-- name    : AlgebraicGeometry.Smooth.smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/cec306e4-e3dc-5511-91e0-33221a3393a0
-- title:
--   Tangent lines at positive-characteristic geometric points force relative dimension 1
-- statement:
--   Let $R$ be a commutative ring of finite type over $\mathbb{Z}$, let $X$ be a scheme, and let $f : X \to \operatorname{Spec} R$ be a morphism that is locally of finite type and smooth. Write $k[\varepsilon] =$ `DualNumber k` for the dual numbers over a field $k$, with structural inclusion $k \to k[\varepsilon]$ and with the projection $\varepsilon \mapsto 0$ given by `TrivSqZeroExt.fstHom k k k`. Assume the following: for every algebraically closed field $k$ of characteristic $\ell$ a prime, and every geometric point $x : \operatorname{Spec} k \to X$, there is a morphism $v : \operatorname{Spec} k[\varepsilon] \to X$ such that $f \circ v = f \circ x \circ \operatorname{Spec}(k \to k[\varepsilon])$ and $v \circ \operatorname{Spec}(\varepsilon \mapsto 0) = x$, and such that every $t : \operatorname{Spec} k[\varepsilon] \to X$ satisfying these same two conditions (namely $f \circ t = f \circ x \circ \operatorname{Spec}(k \to k[\varepsilon])$ and $t \circ \operatorname{Spec}(\varepsilon \mapsto 0) = x$) is of the form $t = v \circ \operatorname{Spec}(\sigma_c)$ for a unique $c \in k$, where $\sigma_c$ is the endomorphism of $k[\varepsilon]$ obtained from `TrivSqZeroExt.map` applied to $c \cdot \mathrm{id}_k$, i.e. $\varepsilon \mapsto c\varepsilon$. The conclusion is that $f$ satisfies `SmoothOfRelativeDimension 1`, that is, $f$ is smooth of relative dimension $1$. Note that the tangent-space hypothesis is imposed only at geometric points of positive characteristic.
--
--   This is a pointwise criterion for a smooth morphism over an affine base of finite type over $\mathbb{Z}$ to have relative dimension $1$: it suffices that the relative tangent space at each geometric point of positive residue characteristic be a line, spanned by the exhibited vector $v$. It is used to verify that the curve representing a fine moduli problem for quaternionic abelian surfaces is a relative curve, in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int

    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [Smooth f]

    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (x : Spec (CommRingCat.of k) ⟶ X),
      ∃ v : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
        v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ x ≫ f ∧
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ v = x ∧
        ∀ t : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
          t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ x ≫ f →
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ t = x →
          ∃! c : k, t = Spec.map (CommRingCat.ofHom
            (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫ v) :
    SmoothOfRelativeDimension 1 f := by sorry
