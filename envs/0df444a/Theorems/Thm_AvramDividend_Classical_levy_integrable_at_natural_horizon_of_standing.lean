-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_integrable_at_natural_horizon_of_standing
-- name    : AvramDividend.Classical.levy_integrable_at_natural_horizon_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:32:14.86448+00:00
-- url     : https://prove2.me/theorems/b0739be0-4c7b-4dab-9bae-4ea552229c12
-- title:
--   Standing Lévy integrability extends to all integer horizons
-- statement:
--   Under the standing Avram hypotheses the increment X_1 is integrable. For every natural n, the Lévy process X_n is also integrable, since each increment X_(k+1)-X_k has the same distribution as X_1 and a finite sum of integrable random variables is integrable. This supplies a concrete localisation time S chosen as an integer strictly exceeding an arbitrary finite horizon T, discharging hXI in the canonically Proved surviving capped Stieltjes dividend reward and cash-integrability results. The argument depends on stationary increments and Integrable.add, with no unproved generator/Itô assumption.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_integrable_at_natural_horizon_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (n : ℕ) : Integrable (X.X (n : ℝ≥0)) P := by sorry
