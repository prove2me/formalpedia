-- Prove2me | Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_measurable
-- name    : AvramDividend.Classical.canonical_drifted_brownian_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:40:25.914404+00:00
-- url     : https://prove2.me/theorems/26d364f6-4895-4958-98b4-7daada451a55
-- title:
--   Canonical normalised and drifted Brownian coordinates are measurable
-- statement:
--   Every coordinate of the canonical continuous Brownian modification is measurable. Taking differences of two coordinates and subtracting a deterministic time preserves measurability. This is needed to construct the natural filtration and the exact Avram Lévy-process adaptedness field.
-- source:
--   Canonical Brownian Kolmogorov–Chentsov modification measurable-coordinate certificate.

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Mathlib.Probability.Process.Filtration

open ProbabilityTheory MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.canonical_drifted_brownian_measurable
    (t : ℝ≥0) :
    Measurable (fun ω : ℝ≥0 → ℝ =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ)) := by sorry
