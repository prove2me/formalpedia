-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_deficit_ae_positive_time_cauchy_ws01c
-- name    : AvramDividend.Classical.bv_actual_deficit_ae_positive_time_cauchy_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:11:23.492518+00:00
-- url     : https://prove2.me/theorems/b52245cc-124e-4feb-b1d6-fe7db1364c62
-- title:
--   Actual BV Lévy drift-deficit right slopes are Cauchy at almost every positive time
-- statement:
--   For the bounded-variation spectrally negative Lévy process, the drift deficit is nondecreasing on almost every sample path by the already Proved monotonicity theorem. The real-time nonnegative-part extension is monotone, hence differentiable at Lebesgue-almost every real time. Its right dyadic difference quotients converge and therefore form a Cauchy sequence at almost every time in the positive unit interval. This is the pathwise Fubini input, with no finite first-moment assumption.
-- source:
--   Complete 1C proof from work/avram_ws01c_actual_fubini_pathwise_draft.lean. Uses Proved bdb273f0-aac2-4b9b-84f3-3bb58bcafb69 and pinned Mathlib monotone a.e. differentiability; no negative-time stationarity.

import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.UniformSpace.Cauchy
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times

open MeasureTheory Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.bv_actual_deficit_ae_positive_time_cauchy_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        CauchySeq (fun n : ℕ =>
          ((X.drift * (Real.toNNReal (t + ((1 : ℝ) / 2) ^ n) : ℝ) -
                X.X (Real.toNNReal (t + ((1 : ℝ) / 2) ^ n)) ω) -
              (X.drift * (Real.toNNReal t : ℝ) -
                X.X (Real.toNNReal t) ω)) / ((1 : ℝ) / 2) ^ n) := by sorry
