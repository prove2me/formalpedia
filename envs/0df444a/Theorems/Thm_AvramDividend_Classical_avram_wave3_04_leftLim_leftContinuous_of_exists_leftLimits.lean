-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
-- name    : AvramDividend.Classical.avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:28:23.50499+00:00
-- url     : https://prove2.me/theorems/ed804a27-2f90-48f6-ae95-da4acf17e44e
-- title:
--   Finite left limits yield left-continuity of the left-limit process on nonnegative time
-- statement:
--   A real-valued path on the nonnegative real time axis with a finite left limit at every strictly positive time admits a left-limit modification which is left-continuous at every nonnegative time, including zero. At positive times the genuine limit identifies Function.leftLim via leftLim_eq_of_tendsto; at zero the left neighbourhood filter is bottom and continuity is automatic. This is a deterministic path-regularity bridge towards predictable controlled Lévy stochastic integrands.
-- source:
--   Pinned Mathlib continuousWithinAt_leftLim_Iic, leftLim_eq_of_tendsto, nhdsLT_neBot_of_exists_lt. Private remote compiler job eb6a8e8f-ef3d-4ebc-acdc-715be9738353 reached sentinel with no candidate errors, exact source SHA-256 cc7e967b0b0282ef1997826ad908b0f1087cf67af10e8a95e423f6adead7f609.

import Mathlib

open Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
    (f : ℝ≥0 → ℝ)
    (hleft : ∀ t : ℝ≥0, 0 < t →
      ∃ l : ℝ, Filter.Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l)) :
    ∀ t : ℝ≥0, ContinuousWithinAt (Function.leftLim f) (Set.Iic t) t := by sorry
