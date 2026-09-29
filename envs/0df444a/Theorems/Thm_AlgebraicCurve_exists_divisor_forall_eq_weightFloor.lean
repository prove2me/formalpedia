-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_divisor_forall_eq_weightFloor
-- name    : AlgebraicCurve.exists_divisor_forall_eq_weightFloor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/2481fa8e-e5c7-5074-ae56-61e602d63890
-- title:
--   Existence of the weight-m floor divisor on a curve
-- statement:
--   Let $K$ be a field and $F$ a field equipped with a $K$-algebra structure satisfying [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15), i.e. (i) $F$ has principal divisors over $K$: every $f \neq 0$ in $F$ admits a finitely supported function $D$ on the places with $D(v) = \operatorname{ord}_v f$ for all $v$ and $\deg D = 0$, (ii) for every place $v$ the residue field of the associated valuation subring is a finite $K$-module, and (iii) $\Omega[F/K]$ is a free $F$-module of rank $1$. Here a place is a valuation subring of $F$ that contains the image of $K$, is not all of $F$ and is a principal ideal ring, $\operatorname{ord}_v$ is minus the logarithm of its $\mathbb{Z}^{m0}$-valued adic valuation, and a divisor is a finitely supported function from places to $\mathbb{Z}$. Let $y \in F$ and $m \in \mathbb{N}$. Then there exists a divisor $D$ such that for every place $w$,
--   $$D(w) = \left[\operatorname{ord}_w y > 0\right]\,\frac{2m\,\operatorname{ord}_w y}{3} + \left[\operatorname{ord}_w(y-1728) > 0\right]\,\frac{m\,\operatorname{ord}_w(y-1728)}{2} + \left[\operatorname{ord}_w y < 0\right]\, m\,\operatorname{ord}_w y,$$
--   the two fractions being integer division, which in the branches where they occur (nonnegative numerator, positive denominator) is the floor. Thus the assertion is exactly that the right-hand side, as a function of $w$, has finite support.
--
--   This is the weight-$m$ floor divisor attached to $y$ on a curve, the divisor of $(dy)^{m}$ corrected at the points of ramification of order $2$ and $3$ when $y$ is a modular invariant; it is the function-field-theoretic form of the divisor used in the Riemann–Roch computation of dimensions of spaces of modular forms. It is invoked for the $\Gamma_1$-case dimension formulae and in producing the corresponding divisor on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_divisor_forall_eq_weightFloor.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.exists_divisor_forall_eq_weightFloor
    (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    (y : F) (m : ℕ) :
    ∃ D : AlgebraicCurve.Divisor K F, ∀ w : AlgebraicCurve.Place K F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0) := by sorry
