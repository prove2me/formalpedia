-- Prove2me | Theorems.Thm_AlgebraicGeometry_isReduced_pullback_of_isReduced_pullback_of_perfectField
-- name    : AlgebraicGeometry.isReduced_pullback_of_isReduced_pullback_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/c97159eb-96f1-54a6-a63c-b74df72dc8ef
-- title:
--   Reducedness of field fibres descends from a perfect subfield
-- statement:
--   Let $f\colon X\to S$ be a morphism of schemes (all in a fixed universe) that is locally of finite type. Let $\kappa_0$ be a perfect field and $x_0\colon \operatorname{Spec}\kappa_0\to S$ a $\kappa_0$-valued point of $S$, and assume the fibre product $X\times_S\operatorname{Spec}\kappa_0$ is a reduced scheme. Let $k$ be a further field, $\iota\colon\kappa_0\to k$ a ring homomorphism, and $x\colon\operatorname{Spec}k\to S$ a $k$-valued point of $S$ which factors through $x_0$ along $\iota$, in the sense that $x$ is the composite of $\operatorname{Spec}(\iota)\colon\operatorname{Spec}k\to\operatorname{Spec}\kappa_0$ followed by $x_0$. The conclusion is that the fibre product $X\times_S\operatorname{Spec}k$, formed along $f$ and $x$, is again reduced. No separability, finiteness or algebraic hypothesis is imposed on the extension $\iota$; perfectness is required only of the smaller field $\kappa_0$, and finite type is required only of $f$.
--
--   This is the standard propagation of reducedness of a field-valued fibre from a perfect field to an arbitrary field extension of it, resting on the fact that for schemes locally of finite type over a perfect field reducedness is automatically geometric (EGA IV$_2$ 4.6; Stacks Project, geometrically reduced schemes). It is used to pass from a description of a special fibre over $\overline{\mathbb F}_p$ to reducedness of the corresponding fibre over any field extension, and is invoked in the analysis of the fibres of the integral models of modular curves and in the counting statement [`AlgebraicGeometry.isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed`](thm.html#AlgebraicGeometry.isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isReduced_pullback_of_isReduced_pullback_of_perfectField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_pullback_of_isReduced_pullback_of_perfectField
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {κ₀ : Type u} [Field κ₀] [PerfectField κ₀] (x₀ : Spec (CommRingCat.of κ₀) ⟶ S)
    [IsReduced (pullback f x₀)]
    {k : Type u} [Field k] (ι : κ₀ →+* k) (x : Spec (CommRingCat.of k) ⟶ S)
    (hx : x = Spec.map (CommRingCat.ofHom ι) ≫ x₀) :
    IsReduced (pullback f x) := by sorry
