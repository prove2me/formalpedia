-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
-- name    : AlgebraicCurve.Place.exists_integralClosureAt_of_ord_fiber_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/27d851e1-8099-5925-8554-9a4a766e7f1b
-- title:
--   No poles above v implies integrality over mathcal Oᵥ
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields, with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$ compatibly (a scalar tower), and assume $F'/F$ is finite-dimensional and separable. Let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing the image of $K$, different from all of $F$, and whose ring is a principal ideal ring; assume moreover that $F'$ over $K$ has principal divisors, in the sense that every nonzero element of $F'$ has a finitely supported divisor whose coefficient at each place is the order of the element there and whose degree is $0$. Let $f \in F'$ be nonzero, and suppose that $0 \le \operatorname{ord}_w(f)$ for every place $w$ of $F'$ over $K$ in the fibre of $v$, i.e. for every $w$ whose restriction to $F$ is $v$, where $\operatorname{ord}_w$ is minus the logarithm of the associated $\mathbb Z^{m0}$-valued adic valuation. The conclusion is that $f$ lies in the image of the integral closure of the valuation ring of $v$ inside $F'$: there exists $c$ in that integral closure with $\operatorname{algebraMap} c = f$.
--
--   This is the statement that the integral closure $C_v$ of $\mathcal O_v$ in $F'$ consists exactly of the functions with no pole at any place of $F'$ above $v$, the places above $v$ corresponding to the height one primes of $C_v$. It serves as the reduction-to-the-integral-case step underlying the local norm and trace formulas, and is cited by the results expressing the norm and the trace of a function at a place as a product and a sum over the fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_integralClosureAt_of_ord_fiber_nonneg {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (hord : ∀ w ∈ v.fiber F', 0 ≤ w.ord f) : ∃ c : Place.integralClosureAt F' v, algebraMap (Place.integralClosureAt F' v) F' c = f := by sorry
