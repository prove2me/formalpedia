-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_compensated_J_tendsto_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_compensated_J_tendsto_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T05:44:56.105799+00:00
-- url     : https://prove2.me/theorems/690384af-dc94-47b0-a6e0-768377dad7ca
-- title:
--   Compensated small-jump integrals converge to small-jump first moment
-- statement:
--   For a bounded-variation spectrally negative Levy process, the normalised compensated small-jump integrals J((n:ℝ)+1) converge to the small-jump first moment A, with no Standing assumption. Helper D1 isolating the J-tendsto step of the drift-positive eventual-growth argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.p2m81_bv_compensated_J_tendsto_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    Tendsto (fun n : ℕ => ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 - ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) atTop (nhds (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0)))) := by sorry
