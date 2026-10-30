-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_genuine_finite_horizon_killed_expectation_no_mesh
-- name    : AvramDividend.Classical.avram_ws01b_bv_genuine_finite_horizon_killed_expectation_no_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:54:41.334613+00:00
-- url     : https://prove2.me/theorems/4c9b501e-d19e-498f-bc4e-da2352c9c052
-- title:
--   Original bounded variation killed expected qscale without mesh parameters
-- statement:
--   Under the actual Standing BV Lévy law, every finite killed two-sided horizon stopped qscale payoff is Bochner integrable and has expectation Wq(x), including x=0, with no auxiliary grid, mesh, or exponential moment assumptions.
-- source:
--   Source original killed finite-horizon expectation and published unconditional BV moment theorem, instantiated at dyadic positive vanishing mesh.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_genuine_finite_horizon_killed_expectation_unconditional

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_genuine_finite_horizon_killed_expectation_no_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    (let Z : Ω → ℝ := fun ω =>
      if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
        if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min (min
            (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
              W (x + X.X (min (min
                (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else if twoSidedExitDownTime X (-x) ω <
              twoSidedExitUpTime X (a-x) ω then 0
      else Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω);
    Integrable Z P ∧ (∫ ω, Z ω ∂P) = W x) := by sorry
