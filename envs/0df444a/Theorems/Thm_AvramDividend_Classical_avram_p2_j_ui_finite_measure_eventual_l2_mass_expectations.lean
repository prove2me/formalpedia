-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:17:33.166995+00:00
-- url     : https://prove2.me/theorems/2298bfb3-ee40-4f82-8fcc-2e3e975e7f95
-- title:
--   Finite-exceptional-prefix L2 Vitali convergence on a finite measure without probability normalisation
-- statement:
--   Let mu be a finite measure and let Y_n converge almost everywhere to Z. Assume only an eventual uniform L2 bound after N and a finite NNReal bound R on the square root of total mass. Then Z is integrable and genuine Bochner expectations of the original unshifted sequence converge. The first N grids need not satisfy the L2 bound; shifting by N is cofinal in atTop.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_l2_mass_bound_expectations

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Discarding finitely many bad grid indices preserves the finite-measure L2 Vitali limit. -/

theorem AvramDividend.Classical.avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (B R : ℝ≥0) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hB : ∀ n, N ≤ n → eLpNorm (Y n) 2 μ ≤ (B : ENNReal))
    (hMass : (μ Set.univ) ^ (1 / 2 : ℝ) ≤ (R : ENNReal))
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by sorry
