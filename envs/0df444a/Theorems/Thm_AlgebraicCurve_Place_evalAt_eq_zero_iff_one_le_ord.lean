-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
-- name    : AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/1f1eb14c-5226-51a2-b85e-bd0131c7d687
-- title:
--   Vanishing at a rational place means order at least one
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $x$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal{O}_x \subseteq F$ containing the image of $K$, different from $F$ itself, and whose underlying ring is a principal ideal ring. Assume $x$ is rational, in the sense that the structure map $K \to \kappa(x)$ into the residue field $\kappa(x) = \mathcal{O}_x/\mathfrak{m}_x$ is surjective. Let $f \in F$ with $f \neq 0$ and $f \in \mathcal{O}_x$. Then the evaluation $x.\mathrm{evalAt}\, f$ — the value in $K$ obtained by applying a chosen set-theoretic inverse of $K \to \kappa(x)$ to the residue class of $f$, this being the definition of [`AlgebraicCurve.Place.evalAt`](def/AlgebraicCurve_PlaceEvaluation.html#L36) on elements of $\mathcal{O}_x$ (and $0$ off $\mathcal{O}_x$) — vanishes if and only if $1 \le \mathrm{ord}_x f$, where $\mathrm{ord}_x f$ is minus the logarithm of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime associated with $x$.
--
--   This is the basic compatibility between the evaluation map at a rational place and the normalised order function: for a non-zero function regular at $x$, vanishing at $x$ is the condition $\mathrm{ord}_x f \ge 1$. The two non-degeneracy hypotheses ($f \neq 0$ and $f \in \mathcal{O}_x$) exclude the regimes in which `evalAt` and `ord` take their default values. It is used throughout the local analysis of functions on modular curves, for instance in computing orders and evaluations on annuli and in the stack order bookkeeping.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : Place K F) (hx : x.IsRational) {f : F} (hf0 : f ≠ 0) (hf : f ∈ x.toValuationSubring) :
    x.evalAt f = 0 ↔ 1 ≤ x.ord f := by sorry
