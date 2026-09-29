-- Prove2me | Theorems.Thm_AlgebraicCurve_WeilDatum_addLeft_pairing
-- name    : AlgebraicCurve.WeilDatum.addLeft_pairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/48c99e2f-7d0f-539d-b208-56d9d9e265f1
-- title:
--   Multiplicativity of the Weil pairing in the first argument
-- statement:
--   Let $K \subseteq F$ be fields ($F$ a $K$-algebra) and let $n$ be a natural number. A `WeilDatum K F n` consists of two divisors $D_1, D_2$ (finitely supported $\mathbb{Z}$-valued functions on the set of places of $F/K$, a place being a proper valuation subring of $F$ containing the image of $K$ whose valuation ring is a principal ideal ring), together with nonzero $f_1, f_2 \in F$ satisfying $\operatorname{ord}_v f_1 = n\,D_1(v)$ and $\operatorname{ord}_v f_2 = n\,D_2(v)$ for every place $v$, such that for each $v$ at least one of $D_1(v), D_2(v)$ vanishes, and such that every $v$ in the support of $D_1$ or of $D_2$ is rational, i.e. $K$ surjects onto the residue field of $v$. The pairing attached to such a datum $d$ is the element $\operatorname{evalFun}(f_1, D_2) / \operatorname{evalFun}(f_2, D_1)$ of $K$, where $\operatorname{evalFun}(f, D) = \prod_v \operatorname{evalAt}_v(f)^{D(v)}$. Given two data $d, d'$ of the same order $n$ with $d.D_2 = d'.D_2$ and $d.f_2 = d'.f_2$, the datum $d.\mathrm{addLeft}\,d'$ has first divisor $d.D_1 + d'.D_1$, second divisor $d.D_2$, first function $d.f_1 \cdot d'.f_1$ and second function $d.f_2$. The theorem asserts that the pairing of this datum equals the product of the pairings of $d$ and $d'$.
--
--   This is multiplicativity (bilinearity in the first variable) of Weil's construction of the pairing $e_n$ through functions with divisor $n D$, formulated on explicit data rather than on divisor classes. It is used in the passage from such data to an additive homomorphism on the $n$-torsion of the degree-zero divisor class group, via [`AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing`](thm.html#AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_WeilDatum_addLeft_pairing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_WeilDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.WeilDatum.addLeft_pairing {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) : (d.addLeft d' hD hf).pairing = d.pairing * d'.pairing := by sorry
