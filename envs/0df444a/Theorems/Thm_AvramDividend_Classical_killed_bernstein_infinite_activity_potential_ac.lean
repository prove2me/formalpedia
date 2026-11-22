-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_bernstein_infinite_activity_potential_ac
-- name    : AvramDividend.Classical.killed_bernstein_infinite_activity_potential_ac
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T15:34:31.604936+00:00
-- url     : https://prove2.me/theorems/e58a6ed6-c4db-4aa7-9af3-e7e6ea3941c0
-- title:
--   Full atomless Lebesgue-AC killed Bernstein potential for infinite activity
-- statement:
--   For a σ-finite Lévy kernel κ supported on t>0 with finite compensated exponential integrals, infinite small-jump mass and Lebesgue absolute continuity, and a strictly positive killing rate k, construct the unique finite killed potential U. It has mass 1/k, is absolutely continuous and atomless on (0,∞), and its exact Laplace transform equals 1/(k+∫(1−e^(−st))dκ). This nontrivial analytic construction decomposes into independent existence by geometric approximations and tight weak limits, and AC/atomlessness via Laplace-derivative convolution. It is the general analytic source required by the original purejump positive Esscher potential; no conclusion about the original scale is assumed.
-- source:
--   Children killed_bernstein_finite_resolvent_measure_exists (5422d653) and killed_bernstein_infinite_ac_resolvent_regular (8c56d3e5); 2fa29eaf rootward via 0cb20c38 original Lévy exponent.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.killed_bernstein_infinite_activity_potential_ac
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (k : ℝ) (hk : 0 < k)
    (hFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤)
    (hκac : κ ≪ (volume : Measure ℝ))
    (hκinf : κ (Ioc (0 : ℝ) 1) = ⊤) :
    ∃ U : Measure ℝ,
      U (Iic (0 : ℝ)) = 0 ∧
      U ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, U {x} = 0) ∧
      U Set.univ = ENNReal.ofReal (k⁻¹) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
          (ENNReal.ofReal k +
            (∫⁻ t : ℝ,
              ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹) := by sorry
