-- Prove2me | Theorems.Thm_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed
-- name    : AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d55a58c6-0fa7-5f62-a8b2-de07f2510811
-- title:
--   Morphisms agreeing on κ-points into a separated scheme
-- statement:
--   Let $\kappa$ be an algebraically closed field (a field with the `IsAlgClosed` property), and let $X$, $Y$ be schemes, all in a single universe. Let $fX : X \to \operatorname{Spec}\kappa$ and $fY : Y \to \operatorname{Spec}\kappa$ be morphisms, where $fX$ is locally of finite type, $X$ is reduced, and $fY$ is separated. Let $f, g : X \to Y$ be morphisms over $\kappa$, that is, $f$ followed by $fY$ equals $fX$ and $g$ followed by $fY$ equals $fX$. Assume that for every morphism $x : \operatorname{Spec}\kappa \to X$ which is a section of $fX$ (i.e. $x$ followed by $fX$ is the identity of $\operatorname{Spec}\kappa$) one has $x$ followed by $f$ equal to $x$ followed by $g$. The conclusion is $f = g$. Thus a $\kappa$-morphism from a reduced $\kappa$-scheme locally of finite type into a scheme separated over $\kappa$ is determined by its effect on $\kappa$-rational points.
--
--   This is the standard rigidity statement that morphisms of $\kappa$-varieties into a separated target are determined by their values on $\kappa$-points, for $\kappa$ algebraically closed. It serves as a general uniqueness tool in the project, being used for instance in the uniqueness clause for morphisms of curve models and in the identification of morphisms between moduli objects in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed
    {κ : Type u} [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of κ)) (fY : Y ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType fX] [IsReduced X] [IsSeparated fY]
    {f g : X ⟶ Y} (hf : f ≫ fY = fX) (hg : g ≫ fY = fX)
    (h : ∀ x : Spec (CommRingCat.of κ) ⟶ X, x ≫ fX = 𝟙 _ → x ≫ f = x ≫ g) :
    f = g := by sorry
