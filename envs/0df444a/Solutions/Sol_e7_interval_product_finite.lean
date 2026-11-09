-- Prove2me | solution 1 for e7_interval_product_finite
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:03:51.380013+00:00
-- url     : https://prove2.me/submissions/799cd44d-8062-45e3-b292-bc3d8060d26e

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (u v : ℝ) (huv : u ≤ v) :
    IsFiniteMeasure ((volume.restrict (Set.uIoc u v)).prod P) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc u v)) := by
    rw [isFiniteMeasure_iff]
    simp [Real.volume_uIoc]
  infer_instance
