-- Prove2me | Theorems.Thm_AlgebraicGeometry_mono_of_formallyUnramified_of_forall_comp_eq
-- name    : AlgebraicGeometry.mono_of_formallyUnramified_of_forall_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/eabc1b0f-4283-5485-9ee1-02a55deda4d6
-- title:
--   Formally unramified and injective on k-points implies mono
-- statement:
--   Let $k$ be an algebraically closed field, and let $X$, $Y$ be schemes (all in a single universe). Let $f : X \to \operatorname{Spec} k$ and $g : Y \to \operatorname{Spec} k$ be morphisms that are locally of finite type, and let $\varphi : X \to Y$ be a morphism over $k$, that is, $\varphi$ followed by $g$ equals $f$, which is formally unramified. Assume further that $\varphi$ is injective on $k$-valued points in the following sense: for any two morphisms $P, Q : \operatorname{Spec} k \to X$ that are sections of $f$ (each composed with $f$ gives the identity of $\operatorname{Spec} k$) and satisfy $P$ followed by $\varphi$ equals $Q$ followed by $\varphi$, one has $P = Q$. The conclusion is that $\varphi$ is a monomorphism in the category of schemes.
--
--   This is the "points" half of the standard criterion that a proper, formally unramified morphism injective on geometric points over an algebraically closed field is a closed immersion (compare EGA IV, 17.2.6): a formally unramified morphism locally of finite type is a monomorphism precisely when its diagonal is an isomorphism. It is used in the derivation of the closed-immersion criterion [`AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq`](thm.html#AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq) and, through that, in an injectivity statement for period maps in the Čerednik–Drinfel'd part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_mono_of_formallyUnramified_of_forall_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.mono_of_formallyUnramified_of_forall_comp_eq
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) [FormallyUnramified φ]
    (hinj : ∀ P Q : Spec (CommRingCat.of k) ⟶ X, P ≫ f = 𝟙 _ → Q ≫ f = 𝟙 _ → P ≫ φ = Q ≫ φ → P = Q) :
    Mono φ := by sorry
