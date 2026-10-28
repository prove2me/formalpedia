-- Prove2me | Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_zero_continuous
-- name    : AvramDividend.Classical.canonical_drifted_brownian_zero_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:18:10.650002+00:00
-- url     : https://prove2.me/theorems/cdf1d3d9-c0c4-4652-a5ec-b7983883abe3
-- title:
--   Canonical Brownian motion, normalised at zero and shifted by drift, starts at zero and has continuous paths everywhere
-- statement:
--   The canonical Brownian process used in the Prove2Me Brownian existence proof has continuous paths for every sample ω. The normalisation X_t=B_t−B_0−t gives X_0=0 exactly for every sample, while deterministic subtraction preserves pathwise continuity. This avoids restricting to an almost-sure good-path subtype when constructing a canonical spectrally negative Lévy counterexample.
-- source:
--   Accepted LevyStochCalc.Brownian.BrownianMotion.exists_readable proof's canonical `ProbabilityTheory.continuous_brownian` construction.

import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

open ProbabilityTheory MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.canonical_drifted_brownian_zero_continuous
    (ω : ℝ≥0 → ℝ) :
    (ProbabilityTheory.brownian 0 ω - ProbabilityTheory.brownian 0 ω - (0 : ℝ)) = 0 ∧
    Continuous (fun t : ℝ≥0 =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ)) := by sorry
