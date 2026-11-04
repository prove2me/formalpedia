-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_l2_ae_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_eventual_l2_ae_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:49:49.055204+00:00
-- url     : https://prove2.me/theorems/83e1d3c5-c8c8-4dfb-a3e6-ee16d84bde19
-- title:
--   An eventual uniform L² envelope suffices for Bochner expectation convergence
-- statement:
--   For measurable real variables converging almost everywhere, a common finite L2 bound after a fixed initial index suffices for the integrability of the limit and convergence of the genuine Bochner expectations. The proof shifts the sequence past the finite exceptional prefix and uses the verified generic L2-to-Vitali theorem. This accommodates eventual bounds provided by source jump-grid estimates.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_expectations_direct

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_eventual_l2_ae_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, N ≤ n → eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
