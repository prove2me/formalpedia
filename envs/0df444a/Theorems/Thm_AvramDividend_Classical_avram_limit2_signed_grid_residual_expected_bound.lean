-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_residual_expected_bound
-- name    : AvramDividend.Classical.avram_limit2_signed_grid_residual_expected_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:56:58.821623+00:00
-- url     : https://prove2.me/theorems/945ac881-b4fa-461f-a87b-dc07367de050
-- title:
--   Genuine signed stopped-grid residual with nonpositive mean yields original expected payoff bound
-- statement:
--   From integrable F and G, exact a.e. source pathwise grid estimate F≤B+G, a genuine nonpositive expected martingale-plus-generator residual G, and the explicit probability normalization E const B = B, Mathlib integral_mono_ae and integral_add produce E F≤B. Repair of a failed publication whose targeted imports lacked real integral notation and the Avram namespace; the mathematical hypotheses are unchanged.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_signed_grid_residual_expected_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F G : Ω → ℝ) (B : ℝ)
    (hF : Integrable F P) (hG : Integrable G P)
    (hConst : (∫ ω : Ω, B ∂P) = B)
    (hPath : ∀ᵐ ω ∂P, F ω ≤ B + G ω)
    (hResidual : (∫ ω, G ω ∂P) ≤ 0) :
    (∫ ω, F ω ∂P) ≤ B := by sorry
