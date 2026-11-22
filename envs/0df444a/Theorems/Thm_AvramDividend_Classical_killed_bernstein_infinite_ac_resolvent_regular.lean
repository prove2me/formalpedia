-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_bernstein_infinite_ac_resolvent_regular
-- name    : AvramDividend.Classical.killed_bernstein_infinite_ac_resolvent_regular
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T15:33:26.971951+00:00
-- url     : https://prove2.me/theorems/8c56d3e5-cd1f-4a0a-ab6a-86f23b5c022b
-- title:
--   Infinite-activity AC Bernstein kernel forces atomless AC killed renewal potential
-- statement:
--   For any positive-half-line absolutely continuous σ-finite Lévy kernel κ with infinite mass on (0,1], and any finite killed Bernstein resolvent measure U already known to have reciprocal-Laplace transform and support [0,∞), prove U is supported in (0,∞), is Lebesgue absolutely continuous and therefore atomless. The atom at zero vanishes because the Bernstein exponent diverges at +∞. For x>0 differentiate reciprocal Laplace transform to obtain xU=(tκ)*U*U, and use AC of tκ together with convolution and Laplace uniqueness. Unlike the first child this is the genuinely nontrivial regularity and renewal atomlessness obstacle.
-- source:
--   Proved original atomless-from-weighted-AC 40d18dd0, generic atomzero 9f464a39, positive convolution Laplace d1bec0b0, unique measure 4fb183cd; original source 2fa29eaf.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.killed_bernstein_infinite_ac_resolvent_regular
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (k : ℝ) (hk : 0 < k)
    (hFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤)
    (hκac : κ ≪ (volume : Measure ℝ))
    (hκinf : κ (Ioc (0 : ℝ) 1) = ⊤)
    (U : Measure ℝ) (hUsupp : U (Iio (0 : ℝ)) = 0)
    (hUmass : U Set.univ = ENNReal.ofReal (k⁻¹))
    (hULap : (∀ s : ℝ, 0 < s →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
          (ENNReal.ofReal k +
            (∫⁻ t : ℝ,
              ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹)) :
    U (Iic (0 : ℝ)) = 0 ∧
    U ≪ (volume : Measure ℝ) ∧
    (∀ x : ℝ, U {x} = 0) := by sorry
