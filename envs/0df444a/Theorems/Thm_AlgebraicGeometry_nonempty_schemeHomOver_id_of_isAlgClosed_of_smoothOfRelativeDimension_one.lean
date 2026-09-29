-- Prove2me | Theorems.Thm_AlgebraicGeometry_nonempty_schemeHomOver_id_of_isAlgClosed_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.nonempty_schemeHomOver_id_of_isAlgClosed_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/7a3a9306-3be5-57c2-8ad3-55441b0da5d8
-- title:
--   Rational point on a smooth proper curve over ̄ k
-- statement:
--   Let $k$ be an algebraically closed field and let $C$ be a scheme (in the bottom universe) equipped with a morphism $c : C \to \operatorname{Spec} k$, where $\operatorname{Spec} k$ is the spectrum of $k$ viewed as a commutative ring object. Assume that $c$ is proper, that $c$ is smooth of relative dimension $1$, and that $c$ satisfies the predicate `GeometricallyIntegral`, expressing geometric integrality of the structure morphism. The conclusion is that the type `SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c` is non-empty, that is: there exists a morphism of schemes $\varphi : \operatorname{Spec} k \to C$ such that $\varphi$ followed by $c$ equals the identity of $\operatorname{Spec} k$. Equivalently, $c$ admits a section over the base, so the set $C(k)$ of $k$-rational points of $C$ is non-empty. The assertion is the bare non-emptiness of the set of sections; no further structure on, or count of, such sections is claimed.
--
--   This is the standard consequence of Hilbert's Nullstellensatz in scheme-theoretic form: a non-empty scheme locally of finite type over an algebraically closed field has a closed point with residue field the base field, hence a rational point. It is used in the study of the special fibre of $X_1(Mp)$, where a section of a component of that fibre is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_nonempty_schemeHomOver_id_of_isAlgClosed_of_smoothOfRelativeDimension_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.nonempty_schemeHomOver_id_of_isAlgClosed_of_smoothOfRelativeDimension_one
    {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) := by sorry
