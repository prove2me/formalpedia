-- Prove2me | Theorems.Thm_AvramDividend_Classical_compensated_jump_integrable
-- name    : AvramDividend.Classical.compensated_jump_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T15:59:12.849989+00:00
-- url     : https://prove2.me/theorems/04e62d2a-6165-4027-b586-f9ca4614e6ac
-- title:
--   Compensated negative-jump kernel is integrable for every nonnegative parameter
-- statement:
--   The exact canonical Avram spectrally negative Lévy integrability field entails integrability of the compensated exponential jump kernel for every theta at least zero. On small negative jumps the remainder is bounded by theta squared times y squared; on large negative jumps it is bounded by one. Together these give domination by (1+theta squared) times min(1,y squared). This discharges the extra integrability hypothesis in the previously proved Gaussian eventual-exponent theorem.
-- source:
--   Exact SpectrallyNegativeLevy.ν_integrable field; Real.add_one_le_exp and exp_neg_remainder_bounds; Lebesgue integral domination theorem in pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped ENNReal NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.compensated_jump_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ =>
      Real.exp (θ * y) - 1 - θ * y *
        ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
      (Iio (0 : ℝ)) X.ν := by sorry
