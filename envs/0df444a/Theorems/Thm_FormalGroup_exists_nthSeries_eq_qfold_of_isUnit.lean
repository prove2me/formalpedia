-- Prove2me | Theorems.Thm_FormalGroup_exists_nthSeries_eq_qfold_of_isUnit
-- name    : FormalGroup.exists_nthSeries_eq_qfold_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/07fe83ce-46b7-57cc-9de8-9f306b004813
-- title:
--   q-fold decomposition [q](T)=qT+qT²h+T^qg
-- statement:
--   Let $R$ be a commutative ring and let $F$ be a one-dimensional formal group law over $R$ which is assumed commutative (the instance `F.IsComm`). Let $q$ be a natural number with $2 \le q$, and assume that for every natural number $k$ with $1 \le k$ and $q \nmid k$ the image of $k$ in $R$ is a unit. Write $[n](T) =$ `F.nthSeries n` for the multiplication-by-$n$ series, defined recursively by $[0](T) = 0$ and $[n+1](T) = F([n](T), T)$, i.e. by substituting the pair $([n](T), T)$ into the two-variable power series underlying $F$. The conclusion is that there exist power series $h, g \in R[[T]]$ with
--   $$[q](T) \;=\; q \cdot T \;+\; q \cdot \bigl(T^2 h(T)\bigr) \;+\; T^q\, g(T),$$
--   where the first summand is the $q$-fold sum of $T$ in $R[[T]]$ and the second is the scalar multiple of $T^2 h(T)$ by the image of $q$ in $R$. No claim is made about the coefficients of $h$ or $g$ beyond their existence.
--
--   This is the structural shape of the multiplication-by-$q$ series of a formal group over a ring in which all integers prime to $q$ are invertible (a $\mathbb{Z}_{(q)}$-algebra, for instance a valuation ring of residue characteristic $q$); classically it is the identity underlying the statement that a formal group over a ring of small absolute ramification has no $q$-torsion. It is used here in the analysis of torsion and of coefficient congruences for `nthSeries`, and in the application to the formal group of a Weierstrass curve over an adically complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_nthSeries_eq_qfold_of_isUnit.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FormalGroup.exists_nthSeries_eq_qfold_of_isUnit {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm] {q : ℕ}
    (hq : 2 ≤ q) (hunit : ∀ k : ℕ, 1 ≤ k → ¬ q ∣ k → IsUnit (k : R)) :
    ∃ h g : PowerSeries R,
      F.nthSeries q = q • PowerSeries.X + (q : R) • (PowerSeries.X ^ 2 * h) + PowerSeries.X ^ q * g := by sorry
