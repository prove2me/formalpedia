-- Prove2me | solution 1 for polynomial_eval_norm_tendsto_cobounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-22T14:36:18.647757+00:00
-- url     : https://prove2.me/submissions/59f0e2a2-70e2-4466-ba5f-13a92e7e9dff

import Mathlib.Analysis.Complex.Polynomial.Basic

open Polynomial Filter


/-!
# Solution — `polynomial_eval_norm_tendsto_cobounded` (Liouville Child 1)

Direct proof via `Polynomial.tendsto_norm_atTop` with `z = id` and the
`cobounded` filter (along which `‖·‖ → ∞`, witnessed by
`tendsto_norm_cobounded_atTop`).
-/

open Polynomial Filter

theorem solution {f : ℂ[X]} (hf : 0 < degree f) :
    Tendsto (fun z : ℂ => ‖f.eval z‖) (Bornology.cobounded ℂ) atTop :=
  f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop
