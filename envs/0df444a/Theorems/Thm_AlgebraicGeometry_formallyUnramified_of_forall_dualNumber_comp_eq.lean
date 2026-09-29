-- Prove2me | Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_dualNumber_comp_eq
-- name    : AlgebraicGeometry.formallyUnramified_of_forall_dualNumber_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/1af07822-6d1b-554f-810b-e847fcae85bd
-- title:
--   Dual-number injectivity implies formal unramifiedness
-- statement:
--   Let $k$ be an algebraically closed field, and let $X$ and $Y$ be schemes (all in a single universe). Let $f : X \to \operatorname{Spec} k$ and $g : Y \to \operatorname{Spec} k$ be morphisms, each locally of finite type, and let $\varphi : X \to Y$ be a morphism compatible with the structure morphisms, i.e. $\varphi$ followed by $g$ equals $f$. Write $k[\varepsilon] =$ `DualNumber k` for the ring of dual numbers over $k$, and let $\sigma : \operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$ denote the morphism induced by the structure map $k \to k[\varepsilon]$. Assume that $\varphi$ is injective on dual-number points over $k$: for all morphisms $P, Q : \operatorname{Spec} k[\varepsilon] \to X$ such that $P$ followed by $f$ equals $\sigma$ and $Q$ followed by $f$ equals $\sigma$, if $P$ followed by $\varphi$ equals $Q$ followed by $\varphi$, then $P = Q$. The conclusion is that $\varphi$ is formally unramified in the sense of Mathlib's `FormallyUnramified` predicate for morphisms of schemes.
--
--   This is the tangent-space half of the standard criterion recognising a morphism as unramified from injectivity on $k[\varepsilon]$-valued points, in the style of EGA IV §17. It feeds the criterion [`AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq`](thm.html#AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq), which upgrades a proper morphism satisfying such point-injectivity hypotheses to a closed immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_formallyUnramified_of_forall_dualNumber_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.formallyUnramified_of_forall_dualNumber_comp_eq
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (hinj : ∀ P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
      P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      P ≫ φ = Q ≫ φ → P = Q) :
    FormallyUnramified φ := by sorry
