-- Prove2me | solution 1 for poly_eventually_const_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-22T14:09:35.159793+00:00
-- url     : https://prove2.me/submissions/e54f95df-b19f-4f42-8c31-3e1af8d2bf60

import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic

open Polynomial Filter Topology


/-!
# Solution — `poly_eventually_const_degree_le` (Child 3)

Direct proof via the identity theorem. `f.eval` is analytic on all of `ℂ`
(`AnalyticOnNhd.eval_polynomial`); it agrees with the constant `f.eval c` on a
neighborhood of `c`, so by `AnalyticOnNhd.eq_of_eventuallyEq` (ℂ is connected)
the two functions are equal everywhere. A polynomial whose evaluation equals a
constant function is that constant polynomial (`Polynomial.funext`), hence has
degree `≤ 0` (`degree_C_le`).

`theorem solution` matches the target type of
`Thm_poly_eventually_const_degree_le`; submit with `proof_type=prove`.
-/

open Polynomial Filter Topology

theorem solution {f : ℂ[X]} {c : ℂ}
    (h : ∀ᶠ z in 𝓝 c, f.eval z = f.eval c) : degree f ≤ 0 := by
  have key : (fun z => f.eval z) = (fun _ : ℂ => f.eval c) :=
    AnalyticOnNhd.eq_of_eventuallyEq (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) f)
      analyticOnNhd_const h
  have hfc : f = C (f.eval c) :=
    Polynomial.funext fun z => by
      have := congrFun key z; simpa using this
  rw [hfc]; exact degree_C_le
