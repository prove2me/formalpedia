-- Prove2me | solution 1 for tendsto_funscale
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:28:32.597289+00:00
-- url     : https://prove2.me/submissions/691a8ac6-332f-4879-aa20-cd4e0ebaf9d4

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
omit [NormedSpace ℝ E]

theorem solution {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) := by
  have hscale : Tendsto (fun R : ℝ => R⁻¹ • x) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const x
  simpa only [funscale, Function.comp_def] using hf.tendsto.comp hscale
