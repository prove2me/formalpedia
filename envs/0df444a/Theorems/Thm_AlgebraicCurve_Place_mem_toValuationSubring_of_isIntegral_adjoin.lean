-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
-- name    : AlgebraicCurve.Place.mem_toValuationSubring_of_isIntegral_adjoin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/afab5c85-24ff-5086-95a7-9e4918ad135f
-- title:
--   Valuation subrings containing j are integrally closed over K[j]
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project: a valuation subring $\mathcal O_v =$ `v.toValuationSubring` of $F$ such that $\mathrm{algebraMap}\,K\,F(a) \in \mathcal O_v$ for every $a \in K$, such that $\mathcal O_v \neq F$, and such that the ring $\mathcal O_v$ is a principal ideal ring. Let $j, x \in F$, assume $j \in \mathcal O_v$, and assume that $x$ is integral over the $K$-subalgebra $\mathrm{Algebra.adjoin}\ K\ \{j\} = K[j]$ of $F$, i.e. $x$ is a root of a monic polynomial with coefficients in $K[j]$. The conclusion is that $x \in \mathcal O_v$. Thus the statement is the integral closedness of $\mathcal O_v$ in $F$ combined with the containment $K[j] \subseteq \mathcal O_v$; the proof uses only that $\mathcal O_v$ is a valuation subring of $F$ containing the image of $K$, not that it is proper or a principal ideal ring.
--
--   This is the standard fact that a valuation ring is integrally closed in its fraction field, packaged for places of a function field $F/K$ and for integrality over a simple $K$-subalgebra $K[j]$. It serves as the bridge used throughout the divisor-theoretic part of the development, for instance when locating the support of a modular unit: it is invoked to conclude that an element integral over $\mathbb Q[j]$ lies in every valuation subring containing $j$, and is cited by the results on orders of such elements and on divisors (for example [`AlgebraicCurve.Place.ord_eq_zero_of_isIntegral_adjoin`](thm.html#AlgebraicCurve.Place.ord_eq_zero_of_isIntegral_adjoin)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.mem_toValuationSubring_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring) (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring := by sorry
