-- Prove2me | Theorems.Thm_AvramDividend_Classical_stieltjes_step_measure_eq_dirac
-- name    : AvramDividend.Classical.stieltjes_step_measure_eq_dirac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T16:55:25.700071+00:00
-- url     : https://prove2.me/theorems/8822f22e-7e81-4fad-ad3d-5306a7fc373d
-- title:
--   The Stieltjes measure of the right-continuous step at the origin is the corresponding atom
-- statement:
--   For $d \ge 0$ let $g(t) = 0$ for $t<0$ and $g(t) = d$ for $t \ge 0$, the right-continuous step at the origin. Then the Lebesgue--Stieltjes measure of $g$ is exactly $d$ times the unit atom at the origin.
--
--   The step is built with `Monotone.stieltjesFunction`, which produces a Stieltjes function whose underlying function is the right limit of the given monotone function. Because $g$ is already right-continuous, this bundle is $g$ itself, and in particular its value at the origin is $d$, not $0$. That is why the case split uses $t<0$ rather than $t\le 0$: the latter is not right-continuous at the origin and would make the stated identity false.
--
--   The measure is characterised on open-closed intervals: for $a<b$ the Stieltjes measure gives $\mathrm{ofReal}\,(g(b)-g(a))$, which is $d$ precisely when $a<0\le b$ and is $0$ otherwise, matching the mass of $(a,b]$ under the atom at $0$.
-- source:
--   Standard property of the Lebesgue-Stieltjes measure of a right-continuous nondecreasing function; uses StieltjesFunction.measure_Ioc together with Measure.ext_of_Ioc from Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stieltjes_step_measure_eq_dirac (d : ℝ) (hd : 0 ≤ d)
    (hf : Monotone (fun t : ℝ => if t < 0 then 0 else d)) :
    hf.stieltjesFunction.measure =
      (ENNReal.ofReal d) • (Measure.dirac (0 : ℝ)) := by sorry
