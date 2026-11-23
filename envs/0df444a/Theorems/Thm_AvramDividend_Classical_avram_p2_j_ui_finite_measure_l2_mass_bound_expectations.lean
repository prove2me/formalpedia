-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_l2_mass_bound_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_finite_measure_l2_mass_bound_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:06:50.088079+00:00
-- url     : https://prove2.me/theorems/5423cf3d-bfcf-46a3-b70d-5275ce329f11
-- title:
--   Finite measure L2 bound and total-mass bound imply a.e.-to-expectation convergence
-- statement:
--   For any finite measure mu, suppose the square root of its total mass is bounded by a finite NNReal R, and the real random variables Y_n have uniform L2 norm bound B. Under almost-everywhere convergence to Z, prove Z integrable and the genuine Bochner expectations converge. Holder supplies an L1 norm bound B*R. This removes explicit global L1 control and probability normalisation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_l2_l1_bound_expectations

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! On finite measures, L2 control and a finite mass bound imply Bochner mean convergence. -/

theorem AvramDividend.Classical.avram_p2_j_ui_finite_measure_l2_mass_bound_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (B R : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hB : ∀ n, eLpNorm (Y n) 2 μ ≤ (B : ENNReal))
    (hMass : (μ Set.univ) ^ (1 / 2 : ℝ) ≤ (R : ENNReal))
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by sorry
