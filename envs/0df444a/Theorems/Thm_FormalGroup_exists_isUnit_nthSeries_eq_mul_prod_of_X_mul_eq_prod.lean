-- Prove2me | Theorems.Thm_FormalGroup_exists_isUnit_nthSeries_eq_mul_prod_of_X_mul_eq_prod
-- name    : FormalGroup.exists_isUnit_nthSeries_eq_mul_prod_of_X_mul_eq_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/130dae96-07d8-598c-a94d-69b82c3a11bd
-- title:
--   Repackaging [q]_F = X g v as a unit times prod (X - cₐ)
-- statement:
--   Let $T$ be a commutative ring and $F$ a one-dimensional formal group law over $T$; for $q \in \mathbb{N}$ write $F.\mathrm{nthSeries}\,q$ for the $q$-th iterate defined recursively by $F.\mathrm{nthSeries}\,0 = 0$ and $F.\mathrm{nthSeries}\,(n+1) = F\bigl(F.\mathrm{nthSeries}\,n,\ X\bigr)$, substitution of the pair $(F.\mathrm{nthSeries}\,n, X)$ into the two-variable power series underlying $F$, i.e. the multiplication-by-$q$ series $[q]_F$. Given a polynomial $g \in T[X]$, a power series $v \in T[\![X]\!]$ that is a unit, and the hypothesis that $F.\mathrm{nthSeries}\,q = X \cdot g \cdot v$ in $T[\![X]\!]$ (with $g$ mapped along the coercion $T[X] \to T[\![X]\!]$), and given a family $c \colon \mathbb{N} \to T$ such that the polynomial identity $X \cdot g = \prod_{a \in \{0,\dots,q-1\}} (X - C(c_a))$ holds in $T[X]$, the conclusion asserts the existence of a unit $u \in T[\![X]\!]$ with $F.\mathrm{nthSeries}\,q = u \cdot \prod_{a \in \{0,\dots,q-1\}} (X - C(c_a))$ in $T[\![X]\!]$. Only the values $c_a$ for $a < q$ enter the statement.
--
--   This is the bookkeeping step that converts a factorisation of the multiplication-by-$q$ series of a formal group into polynomial form, together with a complete splitting of that polynomial into linear factors, into the power-series form 'unit times $\prod_{a<q}(X - c_a)$' in which full sets of $q$-division points are recorded. It is used in the construction of Drinfeld bases on moduli of elliptic curves with level structure, where the roots $c_a$ are the Igusa-type roots attached to a point of the moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_isUnit_nthSeries_eq_mul_prod_of_X_mul_eq_prod.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem FormalGroup.exists_isUnit_nthSeries_eq_mul_prod_of_X_mul_eq_prod
    (T : Type*) [CommRing T] (F : FormalGroup T) (q : ℕ) (g : T[X]) (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)
    (c : ℕ → T) (h : Polynomial.X * g = ∏ a ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a))) :
    ∃ u : PowerSeries T, IsUnit u ∧
      F.nthSeries q = u * ∏ a ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (c a)) := by sorry
