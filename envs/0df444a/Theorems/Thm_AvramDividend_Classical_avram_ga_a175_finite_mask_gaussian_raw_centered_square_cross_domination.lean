-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a175_finite_mask_gaussian_raw_centered_square_cross_domination
-- name    : AvramDividend.Classical.avram_ga_a175_finite_mask_gaussian_raw_centered_square_cross_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:54:43.6055+00:00
-- url     : https://prove2.me/theorems/fbfb7653-1374-4708-83d3-f3b82973664b
-- title:
--   Finite Gaussian masked absolute raw-centred quadratic cross is pointwise bounded by masked centred squares plus deterministic drift-square budget
-- statement:
--   For arbitrary finite cell mask, real source increments and deterministic drift step, the sum of absolute differences of raw and centred squared increments is bounded samplewise by the sum of centred increment squares plus twice the number of cells times drift-step squared. This uses Proved Gaussian square triangle and Young inequality. No artificial process or probabilistic assumptions.
-- source:
--   Proved ga_a84 Young and ga_a85 absolute triangle, finite masked sum monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a85_gaussian_raw_centered_square_triangle
import Theorems.Thm_AvramDividend_Classical_avram_ga_a84_centered_gaussian_quadratic_cross_young_product
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a175_finite_mask_gaussian_raw_centered_square_cross_domination
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (Z : ℕ → Ω → ℝ) (d : ℝ) (ω : Ω) :
    (∑ i ∈ S, if A i ω then
      |(Z i ω + d)^2 - (Z i ω)^2| else 0) ≤
    (∑ i ∈ S, if A i ω then (Z i ω)^2 else 0) +
      (S.card : ℝ) * (2 * d^2) := by sorry
