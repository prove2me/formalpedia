-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber
-- name    : AlgebraicCurve.Place.evalAt_trace_eq_sum_fiber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/5eb217d9-d945-51f4-bcd4-b44436851cdc
-- title:
--   Values of a trace at a rational place
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields, with $F'$ finite-dimensional and separable over $F$ and the tower compatible over $K$. Here a place of a field extension $E/K$ is a valuation subring of $E$ containing the image of $K$, distinct from $E$ itself, and a principal ideal ring; its residue field is that of the local ring in question, $\operatorname{ord}_w$ is minus the logarithm of the associated adic valuation, and $w$ is called rational when the structure map from $K$ to its residue field is surjective, in which case `Place.evalAt` sends an element of the valuation subring to a chosen $K$-preimage of its residue (and sends elements outside the valuation subring to $0$). Assume `HasPrincipalDivisors K F'`: every nonzero element of $F'$ admits a finitely supported divisor recording its orders at all places of $F'/K$ and having degree $0$. Let $v$ be a rational place of $F/K$, and assume every place $w$ in the finite fibre `v.fiber F'` of places of $F'$ over $v$ is rational. Let $f \in F'$ be nonzero with $\operatorname{ord}_w f = 0$ for all $w$ in that fibre. Then the value at $v$ of $\operatorname{Tr}_{F'/F} f$ equals $\sum_{w \mid v} e_w \cdot f(w)$, where $f(w)$ is the value of $f$ at $w$ and $e_w =$ `w.ramificationIndex F` is the least positive natural number of the form $\operatorname{ord}_w(\text{image of a nonzero element of } F)$.
--
--   This is the additive counterpart of the multiplicative formula expressing the value of a norm as a product of values over the fibre, in the classical form $(\operatorname{Tr}_{F'/F} f)(v) = \sum_{w \mid v} e(w\mid v) f(w)$ for a rational place with rational fibre and $f$ a unit along the fibre. It is used in the construction of the Abel–Jacobi correspondence statement [`AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_trace_eq_sum_fiber {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    (f : F') (hf : f ≠ 0) (hord : ∀ w ∈ v.fiber F', w.ord f = 0) :
    v.evalAt (Algebra.trace F F' f) = ∑ w ∈ v.fiber F', w.ramificationIndex F • w.evalAt f := by sorry
