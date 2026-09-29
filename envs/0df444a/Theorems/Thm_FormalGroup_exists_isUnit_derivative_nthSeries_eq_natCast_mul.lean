-- Prove2me | Theorems.Thm_FormalGroup_exists_isUnit_derivative_nthSeries_eq_natCast_mul
-- name    : FormalGroup.exists_isUnit_derivative_nthSeries_eq_natCast_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/291588ea-64eb-5419-97d5-27f81c190a42
-- title:
--   Derivative of [n] on a formal group is n times a unit
-- statement:
--   Let $R$ be a commutative ring and let $F$ be a one-dimensional formal group law over $R$ which is commutative (the instance `F.IsComm`), and let $n$ be a natural number. Here `F.nthSeries n` is the multiplication-by-$n$ series $[n]_F \in R[[Z]]$, defined by recursion: `F.nthSeries 0` is the zero series, and `F.nthSeries (n+1)` is obtained by substituting the pair $(\,[n]_F,\,Z\,)$ into the two-variable power series $F$, i.e. $[n+1]_F(Z) = F([n]_F(Z), Z)$. The assertion is that there exists a power series $u \in R[[Z]]$ which is a unit of $R[[Z]]$ and satisfies $$\tfrac{d}{dZ}[n]_F(Z) = n \cdot u(Z),$$ where the derivative is `PowerSeries.derivative R` and $n$ on the right is the image of the natural number $n$ in $R[[Z]]$, that is, the constant series $n$. No invertibility or finiteness hypotheses on $R$ or $n$ are imposed, and the unit $u$ is produced existentially rather than named.
--
--   This is the standard consequence of the invariance of the differential on a formal group: the multiplication-by-$n$ endomorphism has derivative $n$ up to a unit of $R[[Z]]$, so that $[n]_F$ is unramified wherever $n$ is invertible. It is used by [`FormalGroup.derivative_eval_ne_zero_of_nthSeries_eq_mul`](thm.html#FormalGroup.derivative_eval_ne_zero_of_nthSeries_eq_mul), on the way to the statement that the zeros of $[q]_F$ are simple in characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_isUnit_derivative_nthSeries_eq_natCast_mul.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.exists_isUnit_derivative_nthSeries_eq_natCast_mul
    {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm] (n : ℕ) :
    ∃ u : PowerSeries R, IsUnit u ∧ PowerSeries.derivative R (F.nthSeries n) = (n : PowerSeries R) * u := by sorry
