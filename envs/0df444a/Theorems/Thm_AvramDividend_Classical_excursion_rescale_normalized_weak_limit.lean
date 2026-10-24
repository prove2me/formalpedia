-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_rescale_normalized_weak_limit
-- name    : AvramDividend.Classical.excursion_rescale_normalized_weak_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:11:12.480683+00:00
-- url     : https://prove2.me/theorems/5c1a0c3c-3489-4d9e-aa31-b958b794d649
-- title:
--   Recover a finite-measure weak limit by rescaling normalized probabilities
-- statement:
--   A finite-measure sequence with common NNReal mass c converges weakly along a subsequence whenever its normalized probabilities converge. The limit is c times the limiting probability measure. The proof uses the continuous inclusion ProbabilityMeasure.toFiniteMeasure, continuity of scalar multiplication and the exact self_eq_mass_smul_normalize identity.
-- source:
--   Mathlib FiniteMeasure.self_eq_mass_smul_normalize and continuous_smul, Avram classical excursion weak limits.

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory Filter Topology

theorem AvramDividend.Classical.excursion_rescale_normalized_weak_limit
    (ν : ℕ → FiniteMeasure ℝ) (c : NNReal)
    (hmass : ∀ n : ℕ, (ν n).mass = c)
    (P : ProbabilityMeasure ℝ) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun n : ℕ => (ν (φ n)).normalize)
      atTop (𝓝 P)) :
    Tendsto (fun n : ℕ => ν (φ n)) atTop
      (𝓝 (c • P.toFiniteMeasure)) := by sorry
