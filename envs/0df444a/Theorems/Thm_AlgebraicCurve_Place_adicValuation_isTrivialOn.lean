-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_adicValuation_isTrivialOn
-- name    : AlgebraicCurve.Place.adicValuation_isTrivialOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/5ca17c5e-d2aa-5bb0-ad8c-7d8e397d95c6
-- title:
--   The adic valuation of a place is trivial on the base field
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring $\mathcal{O}_v \subseteq F$ which contains $\mathrm{algebraMap}\,K\,F(a)$ for every $a \in K$, which is not the whole of $F$, and whose ideals are all principal (so that $\mathcal{O}_v$ is a discrete valuation ring). Attached to $v$ is its height one prime [`AlgebraicCurve.Place.heightOneSpectrum`](def/AlgebraicCurve_DivisorClassGroup.html#L95), namely the maximal ideal of $\mathcal{O}_v$ viewed as a point of the height one spectrum, and the associated $\mathbb{Z}^{m0}$-valued adic valuation [`AlgebraicCurve.Place.adicValuation`](def/AlgebraicCurve_DivisorClassGroup.html#L102) on the fraction field $F$, i.e. the normalised valuation whose value group is $\mathbb{Z}$ with a zero adjoined. The theorem asserts that this valuation satisfies `Valuation.IsTrivialOn K`, that is, it is trivial on the image of the base field $K$ in $F$: no element of $K$ has a zero or a pole at $v$.
--
--   This is the standard fact, in the language of algebraic function fields, that a place of $F/K$ is a place over $K$, so that the base field consists of $v$-units; it records the triviality of $v$ on $K$ in a form usable as an instance or hypothesis elsewhere. It is used in the analysis of valuation subrings of a rational function field, via [`AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum`](thm.html#AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_adicValuation_isTrivialOn.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.adicValuation_isTrivialOn {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsTrivialOn K := by sorry
