-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_evalFun_add
-- name    : AlgebraicCurve.Divisor.evalFun_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/350164eb-20df-5284-b994-4d75854593e4
-- title:
--   Multiplicativity of f ↦ f(D) in the divisor
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $f \in F$. A place of $F/K$ in the project's sense is a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$ under the structure map, different from $F$ itself, and whose underlying ring is a principal ideal ring; a divisor is an element of $\mathrm{Place}\,K\,F \to_{f_0} \mathbb{Z}$, i.e. a finitely supported family of integers indexed by such places. For a place $v$, $\mathrm{Place.evalAt}\,v\,f$ is defined to be $0$ when $f \notin \mathcal{O}_v$, and otherwise the image of the residue class of $f$ in the residue field of $\mathcal{O}_v$ under a chosen left inverse (`Function.invFun`) of the map $K \to \mathcal{O}_v/\mathfrak{m}_v$; and for a divisor $D$, $\mathrm{Divisor.evalFun}\,f\,D$ is the finite product $\prod_{v \in \mathrm{supp}\,D} (\mathrm{Place.evalAt}\,v\,f)^{D(v)}$, the exponents being integer powers in the field $K$. Given two divisors $D, E$ such that $\mathrm{Place.evalAt}\,v\,f \neq 0$ for every $v$ in the support of $D$ and for every $v$ in the support of $E$, the theorem states $\mathrm{Divisor.evalFun}\,f\,(D+E) = \mathrm{Divisor.evalFun}\,f\,D \cdot \mathrm{Divisor.evalFun}\,f\,E$.
--
--   This is the additivity in the divisor variable of the local symbol $D \mapsto f(D)$, written multiplicatively; the non-vanishing hypotheses are exactly what is needed to allow negative exponents, since $\mathrm{Place.evalAt}$ takes the value $0$ both at poles of $f$ and at zeros. It is one of the basic manipulations in the layer of evaluation of functions at divisors that underlies Weil reciprocity and the bimultiplicativity of the Weil pairing, and is used for instance in the computation of $\mathrm{evalFun}$ on differences of single-place divisors and in the treatment of the rational function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_evalFun_add.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.evalFun_add {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {D E : Divisor K F} (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) (hE : ∀ v ∈ E.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f (D + E) = Divisor.evalFun f D * Divisor.evalFun f E := by sorry
