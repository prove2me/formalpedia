-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_evalFun_zpow_left
-- name    : AlgebraicCurve.Divisor.evalFun_zpow_left
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/c6a320b6-3073-55e3-85bd-f7ddd21c9292
-- title:
--   Evaluation at a divisor is multiplicative in f ↦ fⁿ
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $f \in F$ be nonzero, let $D$ be a divisor of $F/K$, that is, a finitely supported function from the places of $F/K$ (valuation subrings of $F$ containing the image of $K$, proper in $F$ and principal ideal rings) to $\mathbb{Z}$, and let $n \in \mathbb{Z}$. Assume that every place $v$ in the support of $D$ is rational, meaning that the induced map $K \to \kappa(v)$ to the residue field of the valuation subring of $v$ is surjective, and that $\mathrm{ord}_v f = 0$ for every $v$ in the support of $D$, where $\mathrm{ord}_v$ is the negative of the logarithm of the $v$-adic valuation. Then the evaluation of the $n$-th power $f^n$ (an integer power in the field $F$) at $D$ equals the $n$-th power of the evaluation of $f$ at $D$: with $\mathrm{ev}(g, D) = \prod_{v \in \mathrm{supp}\,D} \mathrm{ev}_v(g)^{D(v)} \in K$, where $\mathrm{ev}_v(g)$ is the preimage in $K$ of the residue class of $g$ when $g$ lies in the valuation subring of $v$ and $0$ otherwise, one has $\mathrm{ev}(f^n, D) = \mathrm{ev}(f, D)^n$.
--
--   This is the elementary multiplicativity of the pairing $(f, D) \mapsto f(D)$ in the first argument restricted to integer powers, at the level of the function-field foundations underlying Weil reciprocity and the Weil pairing. It is used in the computations of evaluations at places of the rational function field, for instance for the place at infinity and for places attached to rational points, and in the degree-one statement over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_evalFun_zpow_left.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.evalFun_zpow_left {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ) (hrat : ∀ v ∈ D.support, Place.IsRational v) (hord : ∀ v ∈ D.support, Place.ord v f = 0) : Divisor.evalFun (f ^ n) D = Divisor.evalFun f D ^ n := by sorry
