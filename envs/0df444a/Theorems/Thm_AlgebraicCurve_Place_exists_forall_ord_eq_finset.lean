-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset
-- name    : AlgebraicCurve.Place.exists_forall_ord_eq_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/b0296bf0-f966-5c0f-8ba5-91df92753aa8
-- title:
--   Prescribing orders at finitely many places
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $\mathrm{Place}\,K\,F$ denote the type of places of $F$ over $K$ in the sense of the project, i.e. of valuation subrings $\mathcal{O}_v \subseteq F$ that contain the image of $K$ under the structure map, are not all of $F$, and are principal ideal rings. Each such $v$ carries the valuation $v.\mathrm{adicValuation}$ with values in $\mathbb{Z}^{m0} = \mathbb{Z} \cup \{0\}$ attached to the associated height-one prime of $\mathcal{O}_v$, and the order function $v.\mathrm{ord}(f) = -\log\bigl(v.\mathrm{adicValuation}(f)\bigr) \in \mathbb{Z}$. The assertion is: for every finite set $S$ of such places and every function $n \colon \mathrm{Place}\,K\,F \to \mathbb{Z}$ (only the values of $n$ on $S$ intervene), there exists $g \in F$ with $g \neq 0$ and $v.\mathrm{ord}(g) = n(v)$ for all $v \in S$; the prescribed orders are attained exactly, not merely approximately, and no condition relating the places or the integers $n(v)$ is imposed.
--
--   This is the independence (weak approximation) statement for finitely many places in the style of Artin–Whaples, in the form that a single nonzero function may be found with arbitrarily prescribed orders at a given finite set of places. It is used in the divisor-theoretic part of the development, for instance in the comparison of pullback and pushforward of divisors along a map of curves and in the recognition of charts of a component from their rings of integers and place maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.exists_forall_ord_eq_finset {K F : Type*} [Field K] [Field F] [Algebra K F] (S : Finset (AlgebraicCurve.Place K F)) (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ g : F, g ≠ 0 ∧ ∀ v ∈ S, v.ord g = n v := by sorry
