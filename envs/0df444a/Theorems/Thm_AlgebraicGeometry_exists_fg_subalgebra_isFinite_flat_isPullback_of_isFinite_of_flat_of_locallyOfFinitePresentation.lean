-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isFinite_flat_isPullback_of_isFinite_of_flat_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.exists_fg_subalgebra_isFinite_flat_isPullback_of_isFinite_of_flat_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/096eedbb-8a43-5412-9a0d-5758b69dfd4e
-- title:
--   Finite flat finitely presented schemes descend to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a Noetherian commutative ring, let $A$ be a commutative $A_0$-algebra, let $X$ be a scheme, and let $g \colon X \to \operatorname{Spec} A$ be a morphism that is finite, flat and locally of finite presentation. Let $s$ be a finite subset of $A$. The assertion is that there exists an $A_0$-subalgebra $T \subseteq A$ which is finitely generated (as an $A_0$-subalgebra, in the sense of `Subalgebra.FG`) and contains $s$, together with a scheme $X_0$, a morphism $f_0 \colon X_0 \to \operatorname{Spec} T$ and a morphism $\pi \colon X \to X_0$, such that $f_0$ is finite, flat and locally of finite presentation, and such that the square formed by $\pi$, $g$, $f_0$ and the morphism $\operatorname{Spec} A \to \operatorname{Spec} T$ induced by the inclusion $T \hookrightarrow A$ is cartesian; that is, $X \cong X_0 \times_{\operatorname{Spec} T} \operatorname{Spec} A$ over $\operatorname{Spec} A$, with $\pi$ the projection to $X_0$. No Noetherian or finiteness hypothesis is imposed on $A$ itself.
--
--   This is the finite-flat member of the standard approximation (limit) package: a finite flat morphism of finite presentation over an arbitrary algebra $A$ over a Noetherian base descends to a finitely generated stage $T$ of $A$, the prescribed finite set $s$ being absorbed into the stage so that finitely many chosen elements of $A$ are already defined over $T$. It is used in the construction of models of fake elliptic curves with level structure over finitely generated subalgebras, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_levelData_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_levelData_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_isFinite_flat_isPullback_of_isFinite_of_flat_of_locallyOfFinitePresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.exists_fg_subalgebra_isFinite_flat_isPullback_of_isFinite_of_flat_of_locallyOfFinitePresentation
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsFinite f₀ ∧ Flat f₀ ∧ LocallyOfFinitePresentation f₀ ∧
        IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by sorry
