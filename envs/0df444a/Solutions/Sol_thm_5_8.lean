-- Prove2me | solution 1 for thm_5_8
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:07:28.561917+00:00
-- url     : https://prove2.me/submissions/ac22b588-0f4b-402f-b66b-fafa9f35e3b8

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_8_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped ENNReal Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_series : (∑' n, P (A n)) ≠ ∞) :
    P (limsup A atTop) = 0 := by
  simpa using MeasureTheory.measure_limsup_atTop_eq_zero (μ := P) (s := A) h_series
