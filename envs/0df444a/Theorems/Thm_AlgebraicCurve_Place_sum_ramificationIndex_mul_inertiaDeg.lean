-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
-- name    : AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/726f87db-1b81-52b1-acd4-0b24e2b78c6e
-- title:
--   Fundamental identity sum_{w∣ v} e f = [F':F]
-- statement:
--   Let $K$, $F$, $F'$ be fields with $K$-algebra structures on $F$ and $F'$ and an $F$-algebra structure on $F'$ forming a scalar tower over $K$, with $F'/F$ finite and separable. A place of $F$ over $K$ is, by definition, a valuation subring of $F$ containing the image of $K$, different from all of $F$, and whose ring is a principal ideal ring; likewise for places of $F'$ over $K$. Assume `HasPrincipalDivisors K F'`, i.e. every nonzero $f \in F'$ admits a divisor $D$ (a finitely supported $\mathbb{Z}$-valued function on the places of $F'$ over $K$) with $D(w) = \mathrm{ord}_w(f)$ at every place $w$ and with degree zero, the degree being the sum of the $D(w)$ weighted by the residue degrees $\deg w$. Then for every place $v$ of $F$ over $K$, summing over the finite set of places $w$ of $F'$ over $K$ whose restriction to $F$ (the preimage valuation subring under $F \to F'$) equals $v$, one has $$\sum_{w \mid v} e(w|v)\, f(w|v) = [F' : F]$$ as integers, where $e(w|v)$ is the least positive integer of the form $\mathrm{ord}_w(f)$ for some nonzero $f \in F$, and $f(w|v)$ is the degree of the residue field of $w$ over the residue field of its restriction to $F$.
--
--   This is the fundamental identity for places of a function field relating ramification indices and residue degrees in a finite separable extension. It is the basic degree computation behind the behaviour of divisors and their degrees under pull-back and push-forward along $F \hookrightarrow F'$, and is used in the theory of the degree-zero divisor class group and in the computation of ramification indices in Kummer-type extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] (v : Place K F) : ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) = (Module.finrank F F' : ℤ) := by sorry
