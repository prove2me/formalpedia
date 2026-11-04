-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_first_moment_limit_uniform_positive_tail
-- name    : AvramDividend.Classical.avram_p2_b_rate_first_moment_limit_uniform_positive_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:40:29.539423+00:00
-- url     : https://prove2.me/theorems/95791c74-b21a-48f2-a4ee-13227b7c779b
-- title:
--   Convergent first moments give an eventual uniform Markov tail envelope
-- statement:
--   For a time-indexed family of Borel measures on the real line, convergence of the ENNReal first positive-part moments to L and any strict bound L<B imply, uniformly over every positive threshold R, the eventual inequality R times mu_h([R,infinity)) <= B. This source-independent quantitative tightness bound can be specialised to the actual original rescaled weighted exponential-image measures using their proved degree-one moment convergence.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_first_moment_limit_uniform_positive_tail
    (μ : ℝ → Measure ℝ) (L B : ℝ≥0∞) (hLB : L < B)
    (hmoment : Tendsto
      (fun h : ℝ => ∫⁻ z : ℝ, ENNReal.ofReal z ∂(μ h))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds L)) :
    ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ R : ℝ, 0 < R →
        ENNReal.ofReal R * μ h (Ici R) ≤ B := by sorry
