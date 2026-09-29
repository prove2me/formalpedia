-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_evalFun_single_sub_single
-- name    : AlgebraicCurve.Divisor.evalFun_single_sub_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/6377aa38-be7b-5094-af93-09470b9e8ee7
-- title:
--   Evaluation of f at a two-point divisor (v₁)-(v₂)
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $f \in F$. A place of $F$ over $K$, in the sense used here, is a valuation subring of $F$ containing the image of $K$ under the structure map, distinct from $F$ itself, and a principal ideal ring; for such a place $v$ the value $v.\mathrm{evalAt}\,f \in K$ is defined to be the preimage under the structure map $K \to \kappa(v)$ (taken via a chosen left inverse) of the residue class of $f$ when $f$ lies in the valuation subring, and $0$ otherwise. A divisor is a finitely supported function from places to $\mathbb{Z}$, and the value $\mathrm{evalFun}\,f\,D$ is the finite product $\prod_{v} (v.\mathrm{evalAt}\,f)^{D(v)}$ over the support of $D$, with integer exponents. The assertion is: given places $v_1, v_2$ with $v_1.\mathrm{evalAt}\,f \neq 0$ and $v_2.\mathrm{evalAt}\,f \neq 0$, the value of $f$ at the divisor written as the sum of the single-point divisors $v_1 \mapsto 1$ and $v_2 \mapsto -1$ equals $(v_1.\mathrm{evalAt}\,f)/(v_2.\mathrm{evalAt}\,f)$. No assumption $v_1 \neq v_2$ is made.
--
--   This is the evaluation of a function at a degree-zero two-point divisor, the basic case underlying local symbols and Weil reciprocity in the function-field layer of the development. It is used in the study of the rational function field, for instance in computing values at the place at infinity and at places attached to points, and in the proof that places have degree one over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_evalFun_single_sub_single.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.evalFun_single_sub_single {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {v₁ v₂ : Place K F} (h₁ : v₁.evalAt f ≠ 0) (h₂ : v₂.evalAt f ≠ 0) : Divisor.evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) = v₁.evalAt f / v₂.evalAt f := by sorry
