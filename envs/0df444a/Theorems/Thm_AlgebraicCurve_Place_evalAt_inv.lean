-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
-- name    : AlgebraicCurve.Place.evalAt_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/9baa1fd8-1922-59dd-b731-2eb081e17700
-- title:
--   Value of an inverse at a rational place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the project's sense: a valuation subring $\mathcal{O}_v \subseteq F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, i.e. the induced map $K \to \mathcal{O}_v/\mathfrak{m}_v$ into the residue field is surjective; evaluation $v.\mathrm{evalAt}$ is then defined on $\mathcal{O}_v$ by composing the residue map with a chosen set-theoretic inverse of $K \to \mathcal{O}_v/\mathfrak{m}_v$, and is set to $0$ off $\mathcal{O}_v$. Let $f \in F$ with $f \neq 0$ and with $\operatorname{ord}_v(f) = 0$, where $\operatorname{ord}_v$ is minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation attached to $v$, so that $f$ has neither a zero nor a pole at $v$. The conclusion is the equality in $K$
--   $$v.\mathrm{evalAt}(f^{-1}) = \big(v.\mathrm{evalAt}(f)\big)^{-1}.$$
--
--   This is the compatibility of evaluation at a rational place with inversion, for functions that are units at the place; it belongs to the layer of elementary properties of evaluating functions at places, underneath the treatment of Weil reciprocity. It is used in the computations with annuli and parameters, for instance when comparing evaluations of a function and of its residue against powers of a parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_inv.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_inv {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) : v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by sorry
