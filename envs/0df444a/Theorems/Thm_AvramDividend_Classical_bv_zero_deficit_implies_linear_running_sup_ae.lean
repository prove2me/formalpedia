-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_zero_deficit_implies_linear_running_sup_ae
-- name    : AvramDividend.Classical.bv_zero_deficit_implies_linear_running_sup_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:00:58.675393+00:00
-- url     : https://prove2.me/theorems/9f967f51-2b7f-430b-b419-59a761848393
-- title:
--   Almost surely the actual BV running supremum equals drift whenever the residual has no jump
-- statement:
--   For every bounded-variation spectrally negative Lévy process meeting Avram's standing conditions, almost surely simultaneously at every time where the drift deficit D_t=d*t-X_t remains zero, its actual running supremum S_t equals d*t. This combines the true all-times subordinator path property, zero-initial-capital axiom, the zero-deficit prefix lemma, the positive standing drift and the proved linear-capital-prefix record identity. It supplies the actual process event-to-record bridge needed to identify zero-barrier Stieltjes dividend payments before the first negative jump.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3 finite-activity zero barrier; accepted actual BV drift deficit path and running-supremum lemmas.

import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_drift_deficit_zero_time_forces_linear_prefix
import Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_zero_deficit_implies_linear_running_sup_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.drift * (t : ℝ) - X.X t ω = 0 →
        runningSup X t ω = X.drift * (t : ℝ) := by sorry
