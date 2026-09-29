-- Prove2me | Theorems.Thm_FormalGroup_coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange
-- name    : FormalGroup.coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/065331e0-8f31-5659-a80c-39a32bd11f9e
-- title:
--   Coefficient of Tᵖ in [p] versus invariant differential
-- statement:
--   Let $p$ be a prime, let $A$ and $R$ be commutative rings with $R$ of characteristic $p$, and assume $A$ has no $p$-torsion, i.e. $pa = 0$ implies $a = 0$ for all $a \in A$. Let `Fl` be a one-dimensional formal group law over $A$, assumed commutative via the class `FormalGroup.IsComm`, let $f : A \to R$ be a ring homomorphism, and let $G$ be a formal group law over $R$ which is the base change of `Fl` along $f$, in the sense that the defining two-variable power series of $G$ is obtained from that of `Fl` by applying $f$ to all coefficients. The conclusion compares two coefficients of one-variable power series over $R$: the coefficient of degree $p$ in `G.nthSeries p`, the $p$-th iterate $[p]$ defined recursively by $[0] = 0$ and $[n+1] = G([n](T), T)$, equals the coefficient of degree $p-1$ in `G.invDiff`, the power series inverse (taken with unit constant term $1$) of $\partial_X G(X,Y)$ evaluated at $X = 0$, $Y = T$, that is of the series $G_X(0,T)$ attached to the invariant differential.
--
--   In characteristic $p$ this identifies the leading new coefficient of the multiplication-by-$p$ series of a formal group with a coefficient of its invariant differential, the formal-group shadow of the Hasse invariant; the hypotheses provide a $p$-torsion-free lift over which $\omega([p])\cdot[p]' = p\,\omega$ may be compared coefficientwise. It is used in the Weierstrass-curve results [`WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant`](thm.html#WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant) and [`WeierstrassCurve.isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet_of_prime`](thm.html#WeierstrassCurve.isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange
    (p : ℕ) [Fact p.Prime] {A R : Type*} [CommRing A] [CommRing R] [CharP R p]
    (hA : ∀ a : A, (p : A) * a = 0 → a = 0)
    (Fl : FormalGroup A) [Fl.IsComm] (f : A →+* R) (G : FormalGroup R) (hG : Fl.IsBaseChange f G) :
    PowerSeries.coeff p (G.nthSeries p) = PowerSeries.coeff (p - 1) G.invDiff := by sorry
