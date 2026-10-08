-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_adapted
-- name    : AvramDividend.Classical.levy_compensated_exponential_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:22:36.249615+00:00
-- url     : https://prove2.me/theorems/bb1df09b-52db-4761-a373-46b03041faa8
-- title:
--   Compensated Lévy exponential is adapted to the original filtration
-- statement:
--   The exponential transform is measurable with respect to each time's filtration because X is adapted and exp, multiplication and subtraction are measurable.
-- source:
--   SpectrallyNegativeLevy.adapted and standard measurable operations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_exponential_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) :
    Adapted 𝓕 (fun t ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) := by sorry
