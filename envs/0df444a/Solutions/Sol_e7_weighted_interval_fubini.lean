-- Prove2me | solution 1 for e7_weighted_interval_fubini
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:59:44.163501+00:00
-- url     : https://prove2.me/submissions/a9ed50da-80cf-4628-9fae-ebbb102a384e

import Mathlib

open MeasureTheory Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {u v : ℝ} (F : ℝ → Ω → ℝ) (W : Ω → ℝ)
    (hprod : Integrable (Function.uncurry (fun w ω => F w ω * W ω))
      ((volume.restrict (Set.uIoc u v)).prod P)) :
    (∫ ω, (∫ w in u..v, F w ω) * W ω ∂P) =
      ∫ w in u..v, (∫ ω, F w ω * W ω ∂P) := by
  rw [intervalIntegral_integral_swap (μ := P) (a := u) (b := v)
    (f := fun w ω => F w ω * W ω) hprod]
  apply integral_congr_ae
  filter_upwards with ω
  exact (intervalIntegral.integral_mul_const (W ω) (fun w => F w ω)).symm
