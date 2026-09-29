-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforward_pullback_of_finite
-- name    : AlgebraicCurve.Divisor.pushforward_pullback_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/a6b1861a-ae17-53ce-a53e-338114bcf5fd
-- title:
--   Pushforward of a pullback divisor is multiplication by [F':F]
-- statement:
--   Let $K \subseteq F \subseteq F'$ be a tower of fields ($F$ and $F'$ are $K$-algebras, $F'$ an $F$-algebra, compatibly as a scalar tower), with $F'/F$ integral, and assume: every nonzero $f \in F'$ has a divisor, i.e. a finitely supported integer-valued function $D$ on the places of $F'/K$ with $D(w) = \operatorname{ord}_w(f)$ for all $w$ and $\deg D = 0$ (`HasPrincipalDivisors K F'`); $F'$ is finite-dimensional over $F$; and the sum–ramification–inertia identity $\sum_{w \in \text{fiber}(v)} e(w\mid F)\, f(w\mid F) = [F':F]$ holds for every place $v$ of $F/K$ (`SumRamificationInertia K F F'`). Here a place of $F/K$ is a valuation subring of $F$ containing $\operatorname{im}(K \to F)$, distinct from $F$ itself and a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$; the restriction $w|_F$ is the preimage valuation subring along $F \to F'$; $e(w\mid F)$ is the least positive value of $\operatorname{ord}_w$ on nonzero elements of $F$; $f(w\mid F)$ is the degree of the residue field of $w$ over that of $w|_F$; $\operatorname{fiber}(v)$ is the (finite) set of places $w$ of $F'/K$ with $w|_F = v$; the pullback sends $\delta_v \mapsto \sum_{w \in \operatorname{fiber}(v)} e(w\mid F)\,\delta_w$ and the pushforward sends $\delta_w \mapsto f(w\mid F)\,\delta_{w|_F}$. Then for every divisor $D$ of $F/K$, the pushforward of the pullback of $D$ equals $[F':F] \cdot D$.
--
--   This is the standard relation $\pi_*\pi^* = \deg$ for divisors on curves, in the place-theoretic language of function fields of one variable. It is used to compare divisors and degree-zero divisor class groups along a finite map, and downstream for pushforward–pullback identities of correspondences and diamond operators on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforward_pullback_of_finite.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforward_pullback_of_finite {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [Module.Finite F F'] [SumRamificationInertia K F F'] (D : Divisor K F) : Divisor.pushforward F (Divisor.pullback F' D) = (Module.finrank F F' : ℤ) • D := by sorry
