-- Prove2me | Theorems.Thm_FormalGroup_subst_nthSeries_invDiff_mul_derivative
-- name    : FormalGroup.subst_nthSeries_invDiff_mul_derivative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/712d8715-1fea-5490-8d8c-58b3b2795917
-- title:
--   Invariance of the invariant differential under [n]
-- statement:
--   Let $R$ be a commutative ring and let $F$ be a one-dimensional formal group law over $R$, assumed commutative (the typeclass `F.IsComm`), and let $n$ be a natural number. Two series attached to $F$ enter. First, the $n$-series `F.nthSeries n`, defined by recursion: `F.nthSeries 0` is the zero power series, and `F.nthSeries (n+1)` is obtained by substituting the pair $(\mathtt{F.nthSeries } n, X)$ into the two-variable series of $F$, so that $[n+1](T) = F([n](T), T)$. Second, the normalised invariant differential `F.invDiff`, defined as `PowerSeries.invOfUnit F.invDiffDenom 1`, the formal inverse of the one-variable series $\mathtt{F.invDiffDenom} = F_X(0,T)$ obtained by substituting $(0, X)$ into the partial derivative `F.partialX` of $F$ in its first variable, the inversion being taken relative to the unit $1$ of $R$ as constant coefficient. The assertion is the identity in $R[[T]]$
--   $$\omega\bigl([n](T)\bigr)\cdot [n]'(T) \;=\; n \cdot \omega(T),$$
--   that is, the substitution of `F.nthSeries n` into `F.invDiff`, multiplied by the formal derivative of `F.nthSeries n`, equals the $n$-fold natural-number multiple $n \bullet$ `F.invDiff`.
--
--   This is the formal-group form of the statement that the pull-back of the invariant differential along multiplication by $n$ is $n$ times the invariant differential, classically obtained by iterating the invariance of $\omega$ under translation by the group law. It is used in the analysis of the $n$-series of a commutative formal group, in particular for the comparison of the coefficients of $[n](T)$ with those of $\omega$, for the extraction of a unit factor from $[n]'(T)$, and for the recognition of $[n](T)$ as a $q$-fold iterate in the unit case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_subst_nthSeries_invDiff_mul_derivative.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FormalGroup.subst_nthSeries_invDiff_mul_derivative {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm] (n : ℕ) :
    PowerSeries.subst (F.nthSeries n) F.invDiff * PowerSeries.derivative R (F.nthSeries n) = n • F.invDiff := by sorry
