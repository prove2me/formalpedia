-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_true_original_stopped_upperstrip_postpre_occupation_indicator_integrable
-- name    : AvramDividend.Classical.avram_gbB54cp_true_original_stopped_upperstrip_postpre_occupation_indicator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:21:58.261686+00:00
-- url     : https://prove2.me/theorems/bd25afc9-d9b0-47cc-9b9d-3c48b51af979
-- title:
--   Original finitecap upper-strip prepayment and postpayment real-time occupancy indicators are integrable on every finite window
-- statement:
--   For any original stopped dividend-control sample path and finite physical time interval (0,n), both the true postpayment reserve upper-cap indicator and the true prepayment riskProcess upper-cap indicator are measurable, bounded by 1 and Lebesgue integrable. This supplies both exact integrability hypotheses required by Proved B50 postpaid-upper-strip-occupation ≤ prepaid-upper-strip-occupation, with no Brownian replacement or source uncertainty. Derive measurability from the source gfinite67 time-sample joint cap strip and B42 real-time postpaid reserve path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB54cp_true_original_stopped_upperstrip_postpre_occupation_indicator_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x b : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (ω : Ω) :
    IntegrableOn
      (fun t : ℝ => if t < (ρ ω : ℝ) ∧
        b < x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume ∧
    IntegrableOn
      (fun t : ℝ => if t < (ρ ω : ℝ) ∧
        b < riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume := by sorry
