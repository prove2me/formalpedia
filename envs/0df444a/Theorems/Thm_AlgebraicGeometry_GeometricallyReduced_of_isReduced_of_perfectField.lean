-- Prove2me | Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
-- name    : AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/83599aca-31de-5d72-9a7e-213d6c3e4088
-- title:
--   Reduced and locally of finite type over a perfect field is geometrically reduced
-- statement:
--   Let $k$ be a perfect field, let $X$ be a scheme, and let $f \colon X \to \operatorname{Spec} k$ be a morphism which is locally of finite type and whose source $X$ is reduced. The conclusion is that $f$ satisfies Mathlib's `GeometricallyReduced` predicate, that is, the property `IsReduced` holds geometrically for $f$: for every base change of $f$ along a field extension of $k$ the resulting scheme is reduced. Concretely, unwinding Mathlib's formulation of the `geometrically` modifier over a commutative base ring, for every field $K$ equipped with a $k$-algebra structure the fibre product $X \times_{\operatorname{Spec} k} \operatorname{Spec} K$, formed along the morphism $\operatorname{Spec} K \to \operatorname{Spec} k$ induced by the structure map $k \to K$, is a reduced scheme; equivalently, any scheme sitting in a pullback square over $f$ and such a morphism is reduced. No properness, separatedness or finiteness of type beyond locally of finite type is assumed, and $k$ is not assumed algebraically closed.
--
--   This is the standard criterion that over a perfect field reducedness is preserved by arbitrary field base change (EGA IV 4.6.1), the scheme-theoretic counterpart of the corresponding statement for finitely generated algebras. It is used in the project whenever geometric reducedness of a fibre must be deduced from reducedness, for instance for fibres over $\mathbb{F}_p$ or over a field of characteristic zero, and is cited by the results on integrality of base changes and on relative Picard groups of curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

theorem AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsReduced X] :
    GeometricallyReduced f := by sorry
