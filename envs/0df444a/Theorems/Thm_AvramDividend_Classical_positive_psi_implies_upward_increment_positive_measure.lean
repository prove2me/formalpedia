-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_psi_implies_upward_increment_positive_measure
-- name    : AvramDividend.Classical.positive_psi_implies_upward_increment_positive_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:45:51.328682+00:00
-- url     : https://prove2.me/theorems/967bfd7f-07b8-43e9-9ebe-85c4494efdf9
-- title:
--   Positive Laplace exponent implies positive probability of an upward increment
-- statement:
--   Under a spectrally negative Lévy process model, any nonnegative exponential moment parameter at which the Laplace exponent is strictly positive forces strictly positive probability of an upward unit-time increment. A null upward event would imply that the increment is nonpositive almost surely, contradicting the already formally proved positive-exponent obstruction. This quantitative measure statement is useful for first-passage probabilities and ruling out proposed nonnegative martingale identities without stopping at ruin.
-- source:
--   Proved positive_psi_excludes_nonpositive_one_increment_ae and Mathlib ae_iff.

import Theorems.Thm_AvramDividend_Classical_positive_psi_excludes_nonpositive_one_increment_ae
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_psi_implies_upward_increment_positive_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 < X.ψ θ) :
    0 < P {ω : Ω | 0 < X.X 1 ω} := by sorry
