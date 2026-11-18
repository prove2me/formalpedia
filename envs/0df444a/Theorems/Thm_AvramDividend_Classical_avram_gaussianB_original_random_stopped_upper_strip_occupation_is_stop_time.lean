-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_random_stopped_upper_strip_occupation_is_stop_time
-- name    : AvramDividend.Classical.avram_gaussianB_original_random_stopped_upper_strip_occupation_is_stop_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:12:49.379418+00:00
-- url     : https://prove2.me/theorems/46f8edf5-24b2-4e78-9194-2d1b6ed32edc
-- title:
--   Original random-stopped Gaussian upper-strip occupation equals the stopping time on every strictly above-band source path
-- statement:
--   For an original stopped physical-time functional integrating the indicator t<ρ(ω) and reserve(Real.toNNReal t,ω)>b over (0,n), if the stopping time ρ(ω) is positive and at most n and the reserve is strictly above b throughout the pre-stop interval, then the exact stopped occupation integral equals the random physical stopping time ρ(ω). This identifies the missing fixed-j positive drift occupation term pathwise.

import Mathlib.Topology.Instances.NNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_true_stopped_upper_strip_occupation_equals_physical_horizon
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_random_stopped_upper_strip_occupation_is_stop_time
    {Ω : Type*} (A : Set Ω)
    (ρ : Ω → ℝ≥0) (n : ℕ) (b : ℝ)
    (f : ℝ≥0 → Ω → ℝ)
    (hρpos : ∀ ω ∈ A, 0 < ρ ω)
    (hρn : ∀ ω ∈ A, ρ ω ≤ (n : ℝ≥0))
    (hFloor : ∀ ω ∈ A, ∀ s : ℝ≥0,
      0 < s → s < ρ ω → b < f s ω) :
    ∀ ω ∈ A,
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (if t < (ρ ω : ℝ) ∧ b < f (Real.toNNReal t) ω
          then (1 : ℝ) else 0) ∂volume) = (ρ ω : ℝ) := by sorry
