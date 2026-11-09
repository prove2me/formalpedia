-- Prove2me | solution 1 for e7_interval_term_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:53:23.122779+00:00
-- url     : https://prove2.me/submissions/005efafd-8d9e-4a5c-8bb1-029a851bc2c4

import Mathlib

open MeasureTheory Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {u v : ℝ} (huv : u ≤ v) (F : ℝ → Ω → ℝ) (W : Ω → ℝ)
    (hprod : Integrable (Function.uncurry (fun w ω => F w ω * W ω))
      ((volume.restrict (Set.uIoc u v)).prod P)) :
    Integrable (fun ω => (∫ w in u..v, F w ω) * W ω) P := by
  rw [Set.uIoc_of_le huv] at hprod
  have hfib : Integrable (fun ω => ∫ w, F w ω * W ω ∂(volume.restrict (Set.Ioc u v))) P :=
    hprod.integral_prod_right
  refine hfib.congr ?_
  filter_upwards with ω
  rw [intervalIntegral.integral_of_le huv]
  rw [← integral_mul_const (W ω) (fun w => F w ω)]
