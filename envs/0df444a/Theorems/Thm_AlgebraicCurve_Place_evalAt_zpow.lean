-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_zpow
-- name    : AlgebraicCurve.Place.evalAt_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/094e6dff-f7be-58f6-880c-e2157f644670
-- title:
--   Evaluation at a rational place respects integer powers
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal O_v \subseteq F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, meaning that the composite $K \to \mathcal O_v \to \mathcal O_v/\mathfrak m_v$ into the residue field is surjective, so that the evaluation map $\mathrm{evalAt}$ — which sends $f \in \mathcal O_v$ to a chosen preimage in $K$ (via `Function.invFun`) of the residue class of $f$, and sends every $f \notin \mathcal O_v$ to $0$ — is a genuine value map with values in $K$. Let $f \in F$ be nonzero and suppose $\mathrm{ord}_v(f) = 0$, where $\mathrm{ord}_v$ is minus the logarithm of the $\mathbb Z^{m0}$-valued valuation attached to the height one prime of $\mathcal O_v$; thus $f$ is a unit of $\mathcal O_v$. Then for every integer $n$, $\mathrm{evalAt}_v(f^{\,n}) = \bigl(\mathrm{evalAt}_v(f)\bigr)^{n}$, the power on the right being taken in $K$.
--
--   This is the multiplicativity of evaluation at a rational place on integer powers of a $v$-unit, i.e. the statement that $f \mapsto f(v)$ is a homomorphism $\mathcal O_v^{\times} \to K^{\times}$ tested against $\mathbb Z$-powers. It belongs to the function-field layer of evaluating functions at places and divisors, and is used in the computation of evaluation along divisors and in the results on residues of evaluations at annuli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_zpow.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_zpow {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) (n : ℤ) : v.evalAt (f ^ n) = v.evalAt f ^ n := by sorry
