-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_ne_zero
-- name    : AlgebraicCurve.RationalFunctionField.deg_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/9cd09f93-3ea8-5bf3-8a57-2218fb4588eb
-- title:
--   Places of K(t) have nonzero degree
-- statement:
--   Let $K$ be a field and let $v$ be a place of the rational function field $\mathrm{RatFunc}\,K$ over $K$ in the sense of the project's structure `Place`: a valuation subring $\mathcal{O}_v$ of $\mathrm{RatFunc}\,K$ that contains $\mathrm{algebraMap}\,K\,(\mathrm{RatFunc}\,K)(a)$ for every $a \in K$, is not the whole field, and is a principal ideal ring. Its degree $v.\mathrm{deg}$ is defined to be the $K$-rank $\mathrm{Module.finrank}\,K$ of the residue field $\mathcal{O}_v/\mathfrak{m}_v$, that is, of `IsLocalRing.ResidueField v.toValuationSubring`, viewed as a $K$-vector space via the structure map. The assertion is that this natural number is nonzero. Since `Module.finrank` returns $0$ both for the zero module and for modules that are not finite-dimensional, the statement simultaneously says that the residue field of every place of $K(t)$ is a finite extension of $K$ and that it is nontrivial; equivalently, the junk value $0$ never occurs, so $v.\mathrm{deg} \geq 1$ always holds.
--
--   This is the statement that the residue degree of a place of a rational function field is finite and positive, the basic finiteness needed before degrees of divisors on $\mathbb{P}^1_K$ can be manipulated. It is used for the non-vanishing of degrees of places in finite extensions of $K(t)$ and, through that, for places of the modular function field and for counting arguments on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_ne_zero.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.deg_ne_zero {K : Type*} [Field K] (v : Place K (RatFunc K)) : v.deg ≠ 0 := by sorry
