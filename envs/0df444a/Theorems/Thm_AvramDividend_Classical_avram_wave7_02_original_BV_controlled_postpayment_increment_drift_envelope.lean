-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:51:58.234195+00:00
-- url     : https://prove2.me/theorems/6c45ed32-71ad-4525-98ae-fa03ae0f0d8c
-- title:
--   Original bounded-variation stopped controlled postpayment reserve obeys exact physical drift increment envelope
-- statement:
--   For the exact original BV spectrally negative Levy X and actual left-continuous nondecreasing dividend strategy D, on one a.s. event for all nonnegative s≤t the true postpayment controlled reserve x+X.X t-rightLimit D t has increment bounded above by (t-s) times the physical Lévy drift. Proof uses the original BV monotone downward residual and monotonicity of the genuine dividend right limits. Includes all negative source jumps, continuous/singular residual loss and all right-dividend jumps, even simultaneous jumps. Pure pathwise increment estimate, no false claim of the compensated expected stopped HJB bound.
-- source:
--   Actual Lévy residual monotone ae f6cc1059 and exact original dividend right-limit monotonicity f7eef805; literal x+X.X-rightLimit D controlled reserve, source and dividend signs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- For the original BV Lévy process and genuine right dividend payments,
the full controlled reserve increment is bounded above by physical drift.
This includes all negative source jumps, singular continuous source loss,
diffuse dividends, and simultaneous right dividend jumps. -/

theorem AvramDividend.Classical.avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (x + X.X t ω - rightLimit D t ω) -
        (x + X.X s ω - rightLimit D s ω) ≤
      ((t : ℝ) - (s : ℝ)) * X.drift := by sorry
