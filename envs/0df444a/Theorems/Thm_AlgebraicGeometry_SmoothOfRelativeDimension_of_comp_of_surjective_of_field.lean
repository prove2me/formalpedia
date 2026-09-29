-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_surjective_of_field
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_surjective_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/7336ace9-cc1e-5985-8ce1-ab0c20693e48
-- title:
--   Smooth descent along a surjection, with relative dimensions
-- statement:
--   Let $k$ be a field, let $G$ and $Q$ be schemes (all in a single universe), with $G$ nonempty, and let $f_Q : Q \to \operatorname{Spec} k$ and $q : G \to Q$ be morphisms of schemes. Let $g$ and $h$ be natural numbers, and assume, as instance hypotheses, that the composite $q$ followed by $f_Q$ is smooth of relative dimension $g$, that $q$ is smooth of relative dimension $h$, and that $q$ is surjective and quasi-compact. The conclusion is a conjunction: $f_Q$ is smooth of relative dimension $g - h$, the subtraction being truncated subtraction in $\mathbb{N}$, and $h \le g$, so that the truncated difference is the genuine one. Nothing about $k$ beyond its commutative ring structure, which is what is needed to form $\operatorname{Spec} k$, enters the argument.
--
--   This is descent of smoothness along a smooth quasi-compact surjection together with additivity of relative dimension (EGA IV 17.7.7 and 17.11.1), specialised to a base that is the spectrum of a field. It is used in the construction of the relative group law on Jacobians of curves with good reduction, where the relative dimension of a group scheme over the base is read off from a surjective smooth action morphism, via [`GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_isPullback_action_of_surjective`](thm.html#GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_isPullback_action_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_surjective_of_field.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_surjective_of_field
    {k : Type u} [Field k] {G Q : Scheme.{u}} [Nonempty G] (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q)
    (g h : ℕ) [SmoothOfRelativeDimension g (q ≫ fQ)] [SmoothOfRelativeDimension h q] [Surjective q]
    [QuasiCompact q] : SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g := by sorry
