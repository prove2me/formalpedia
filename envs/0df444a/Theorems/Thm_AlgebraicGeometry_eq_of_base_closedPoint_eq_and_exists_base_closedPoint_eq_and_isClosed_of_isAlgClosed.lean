-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
-- name    : AlgebraicGeometry.eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/184da560-ff18-52a2-b01f-1dd810f046a6
-- title:
--   κ-points of a finite-type scheme over an algebraically closed field
-- statement:
--   Let $\kappa$ be an algebraically closed field (in a fixed universe), let $Y$ be a scheme and let $f \colon Y \to \operatorname{Spec} \kappa$ be a morphism of schemes that is locally of finite type. Three assertions are made simultaneously. First, any two sections of $f$, i.e. morphisms $y, y' \colon \operatorname{Spec} \kappa \to Y$ with $f \circ y = \mathrm{id}$ and $f \circ y' = \mathrm{id}$, which send the closed point of $\operatorname{Spec} \kappa$ (the unique maximal ideal of $\kappa$, as a point of the underlying space) to the same point of $Y$, are equal as morphisms of schemes. Second, for every point $q$ of $Y$ whose singleton $\{q\}$ is closed in the underlying topological space of $Y$, there exists a morphism $y \colon \operatorname{Spec} \kappa \to Y$ with $f \circ y = \mathrm{id}$ whose underlying map carries the closed point of $\operatorname{Spec} \kappa$ to $q$. Third, if the underlying type of points of $Y$ is finite, then every singleton $\{q\}$ in $Y$ is closed.
--
--   This is the standard identification of $\kappa$-rational points of a scheme locally of finite type over an algebraically closed field $\kappa$ with the closed points of its underlying space, together with the observation that such a scheme with finitely many points is discrete. It serves as the bridge between sections of a structure morphism and closed points in the Čerednik–Drinfeld and fake elliptic curve developments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
    (κ : Type u) [Field κ] [IsAlgClosed κ] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f] :
    (∀ (y y' : Spec (CommRingCat.of κ) ⟶ Y), y ≫ f = 𝟙 _ → y' ≫ f = 𝟙 _ →
        y.base (IsLocalRing.closedPoint κ) = y'.base (IsLocalRing.closedPoint κ) → y = y') ∧
    (∀ q : Y, IsClosed ({q} : Set Y) →
        ∃ y : Spec (CommRingCat.of κ) ⟶ Y, y ≫ f = 𝟙 _ ∧ y.base (IsLocalRing.closedPoint κ) = q) ∧
    (Finite Y → ∀ q : Y, IsClosed ({q} : Set Y)) := by sorry
