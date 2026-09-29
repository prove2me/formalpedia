-- Prove2me | Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
-- name    : AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/332fb08b-5c52-50fb-989b-d8a6ed42a175
-- title:
--   Unit derivatives are regular: du/dπ_w∈mathcal O_w
-- statement:
--   Let $K$ be a perfect field and $F'$ a field extension of $K$ which is essentially of finite type over $K$ and which is a curve over $K$ in the project's sense: every nonzero $f \in F'$ has a principal divisor of degree $0$, each place of $F'$ over $K$ has residue field finite over $K$, and the module of Kähler differentials $\Omega_{F'/K}$ is free of rank one over $F'$. Here a place $w$ is a valuation subring of $F'$ containing the image of $K$, different from all of $F'$, whose ring is a principal ideal ring, and $\operatorname{ord}_w$ is minus the logarithm of the associated height-one adic valuation. Assume in addition that for every place $w$ the single differential $d\pi_w = D_{K}(\pi_w)$ of a chosen uniformiser spans $\Omega_{F'/K}$ over $F'$. Then for every place $w$ of $F'$ over $K$ and every $u \in F'$ with $u \neq 0$ and $\operatorname{ord}_w u = 0$, the coefficient $c$ of $D_K(u)$ with respect to $d\pi_w$ (namely the value of `Place.differentialCoeff`, a choice of $c$ with $D_K(u) = c \cdot d\pi_w$, and $0$ if no such $c$ exists) satisfies: either $c = 0$, or $\operatorname{ord}_w c \geq 0$.
--
--   This is the statement that the logarithmic-type derivative $du/d\pi_w$ of a $w$-unit is regular at $w$, as in the theory of differentials on algebraic function fields; it is the regularity input used by the Riemann–Hurwitz computations of the project, for instance in the computation of orders of differentials, of canonical divisors under maps, and in the residue/degree formulae that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem localUnitDerivativeRegular_of_isCurveOver {K : Type*} {F' : Type*} [Field K] [Field F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates] :
    ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) := by sorry
