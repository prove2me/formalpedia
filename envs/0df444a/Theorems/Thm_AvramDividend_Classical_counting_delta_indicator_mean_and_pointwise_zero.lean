-- Prove2me | Theorems.Thm_AvramDividend_Classical_counting_delta_indicator_mean_and_pointwise_zero
-- name    : AvramDividend.Classical.counting_delta_indicator_mean_and_pointwise_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:34:12.012252+00:00
-- url     : https://prove2.me/theorems/871bd59b-052f-40dd-b003-481339fb6526
-- title:
--   Counting-measure moving singleton has fixed mean and pointwise zero limit
-- statement:
--   Count measure moving singleton has unit Bochner integral for every n but vanishes eventually at every fixed k.
-- source:
--   Finite-mass hypothesis audit for Avram Vitali expectation convergence

import Mathlib
open MeasureTheory Filter Set
noncomputable section

theorem AvramDividend.Classical.counting_delta_indicator_mean_and_pointwise_zero :
    (∀ n : ℕ, (∫ k : ℕ, ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) k
      ∂(Measure.count : Measure ℕ)) = 1) ∧
    (∀ k : ℕ, Tendsto (fun n : ℕ => ({n} : Set ℕ).indicator
      (fun _ => (1 : ℝ)) k) atTop (nhds 0)) := by sorry
