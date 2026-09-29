-- Prove2me | Theorems.Thm_FormalGroup_nthSeries_eq_zero_or_exists_eq_mul_X_pow_pow
-- name    : FormalGroup.nthSeries_eq_zero_or_exists_eq_mul_X_pow_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/caa5cf79-7bb9-5459-b1b6-19d13d7f579f
-- title:
--   Frobenius factorisation of [q]_F in characteristic q
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $F$ a one-dimensional formal group law over $k$ (an element `F : FormalGroup k`, with two-variable law `F.toPowerSeries`) satisfying the predicate `F.IsComm`. Write `F.nthSeries` for the sequence of one-variable power series over $k$ defined by `F.nthSeries 0 = 0` and `F.nthSeries (n+1)` = the substitution of the pair $(\mathtt{F.nthSeries } n, X)$ into the group law `F.toPowerSeries`, i.e. the multiplication-by-$n$ series $[n]_F$. The assertion is a dichotomy for the $q$-th member of this sequence: either `F.nthSeries q` is the zero power series, or there exist a natural number $h$ with $1 \le h$ and a power series $u \in k[[X]]$ which is a unit (equivalently, has invertible constant term) such that $$[q]_F \;=\; \mathtt{F.nthSeries } q \;=\; u \cdot X^{q^{h}}.$$ In particular, when $[q]_F \neq 0$ its order is an exact power $q^h$ of $q$ with $h \ge 1$; the exponent $h$ is the height of $F$.
--
--   This is the classical statement that the multiplication-by-$q$ endomorphism of a commutative formal group law in characteristic $q$ is either zero or a unit multiple of $X^{q^h}$ for some $h \ge 1$, which is how the height of a formal group is defined. It is used in the study of formal groups of elliptic curves in characteristic $p$, being cited by [`WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_pow_or_eq_mul_X_pow_mul`](thm.html#WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_pow_or_eq_mul_X_pow_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_nthSeries_eq_zero_or_exists_eq_mul_X_pow_pow.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.nthSeries_eq_zero_or_exists_eq_mul_X_pow_pow
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (F : FormalGroup k) [F.IsComm] :
    F.nthSeries q = 0 ∨
      ∃ (h : ℕ) (u : PowerSeries k), 1 ≤ h ∧ IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ (q ^ h) := by sorry
