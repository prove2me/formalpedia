-- Prove2me | Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
-- name    : AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/675c7943-897a-581f-a0f7-ad90fb0cc761
-- title:
--   Chordal proximity in a normalised chart
-- statement:
--   Let $L$ be a field and $\nu$ a real-valued absolute value on $L$ which is nonarchimedean, in the sense that $\nu(a+b)\le\max(\nu(a),\nu(b))$ for all $a,b$. Let $r$ be a natural number and let $x,y\colon \mathrm{Fin}\,r\to L$ be two rows of elements of $L$. Assume there is an index $j$ with $x_j=1$ and $y_j=1$ (so in particular $r\ge 1$), and that all entries are in the closed unit ball, $\nu(x_i)\le 1$ and $\nu(y_i)\le 1$ for every $i$. The conclusion is an identity for the chordal proximity of the two rows, which by definition is
--   $$\mathrm{prox}\,\nu\,x\,y=\log\Bigl(\sup_i \nu(x_i)\Bigr)+\log\Bigl(\sup_i \nu(y_i)\Bigr)-\log\Bigl(\sup_{(p,q)}\nu(x_p y_q-x_q y_p)\Bigr),$$
--   the suprema being taken over $\mathrm{Fin}\,r$ and over $\mathrm{Fin}\,r\times\mathrm{Fin}\,r$ respectively. Under the above hypotheses it equals
--   $$-\log\Bigl(\sup_i \nu(x_i-y_i)\Bigr).$$
--   Here the logarithm is the Mathlib real logarithm, so both sides read $0$ when the two rows coincide and the supremum of the differences vanishes.
--
--   An elementary ultrametric comparison identifying the chordal proximity of two points given by unit-ball coordinate vectors normalised to have a common coordinate equal to $1$ with the negative logarithm of the maximal coordinatewise distance. It is the basic computational tool for proximity in a chart, used by the chart-comparison results such as [`AlgebraicCurve.ComponentChart.prox_eq_of_chartData_of_minor`](thm.html#AlgebraicCurve.ComponentChart.prox_eq_of_chartData_of_minor) and by the proximity estimates on the modular curve, for instance [`ModularCurve.JZero.exists_abv_evalAt_eq_abv_evalAt_of_le_prox`](thm.html#ModularCurve.JZero.exists_abv_evalAt_eq_abv_evalAt_of_le_prox) and [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart.lean

import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart {L : Type*} [Field L]
    (ν : AbsoluteValue L ℝ) (hna : IsNonarchimedean ⇑ν) {r : ℕ}
    (x y : Fin r → L) (j : Fin r) (hxj : x j = 1) (hyj : y j = 1)
    (hx : ∀ i, ν (x i) ≤ 1) (hy : ∀ i, ν (y i) ≤ 1) :
    prox ν x y = -Real.log (⨆ i, ν (x i - y i)) := by sorry
