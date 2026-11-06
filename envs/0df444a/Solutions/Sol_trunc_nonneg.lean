-- Prove2me | solution 1 for trunc.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:23:11.791349+00:00
-- url     : https://prove2.me/submissions/5d8d2218-76a2-407b-bace-00f39be3e87c

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open trunc

theorem solution (g : trunc) (x : ℝ) : 0 ≤ g x := by
  exact (Set.indicator_nonneg (fun _ _ => zero_le_one) x).trans (g.h3 x)
