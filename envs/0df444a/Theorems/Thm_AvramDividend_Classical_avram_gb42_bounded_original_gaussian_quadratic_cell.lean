-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb42_bounded_original_gaussian_quadratic_cell
-- name    : AvramDividend.Classical.avram_gb42_bounded_original_gaussian_quadratic_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:52:01.529293+00:00
-- url     : https://prove2.me/theorems/f9ad19ba-2fdc-4f17-890e-5c294d08a783
-- title:
--   Bounded original Gaussian quadratic cell has second moment of order interval squared
-- statement:
--   A measurable bounded predictable coefficient multiplying a centred-square original Gaussian increment has an integrable squared product with second moment at most 8KH² σ⁴ Δ² whenever the normalised fourth moment is bounded by 3Δ².
-- source:
--   Smaller exact analytic substep isolated from gb34. Later instantiated with original stopped Hessian and interval increment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gb42_bounded_original_gaussian_quadratic_cell
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H Z : Ω → ℝ) (σ Δ KH : ℝ) (hσ : 0 < σ) (hKH : 0 ≤ KH)
    (hHm : Measurable H) (hHb : ∀ ω, |H ω| ≤ KH)
    (hZm : Measurable Z)
    (hFourth : (∫⁻ ω, ENNReal.ofReal ((Z ω / σ) ^ 4) ∂P) ≤
      ENNReal.ofReal (3 * Δ ^ 2)) :
    Integrable (fun ω => (H ω * (Z ω ^ 2 - Δ * σ ^ 2)) ^ 2) P ∧
      (∫ ω, (H ω * (Z ω ^ 2 - Δ * σ ^ 2)) ^ 2 ∂P) ≤
        8 * KH ^ 2 * σ ^ 4 * Δ ^ 2 := by sorry
