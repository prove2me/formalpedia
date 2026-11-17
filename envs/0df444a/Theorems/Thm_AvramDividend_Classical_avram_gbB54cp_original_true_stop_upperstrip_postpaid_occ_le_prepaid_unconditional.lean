-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_original_true_stop_upperstrip_postpaid_occ_le_prepaid_unconditional
-- name    : AvramDividend.Classical.avram_gbB54cp_original_true_stop_upperstrip_postpaid_occ_le_prepaid_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:22:33.821846+00:00
-- url     : https://prove2.me/theorems/305ae797-e44f-4b59-9006-babc98c569e1
-- title:
--   Original finite-cap true stopped upper-strip occupation postpayment never exceeds prepayment, without assumed integrability
-- statement:
--   For the original Lévy dividend model, bounded physical horizon and exact random stopping clock, the time integral of the postpayment reserve indicator above the clipping cap b is bounded by the original prepayment riskProcess occupation integral. No auxiliary IntegrableOn assumptions are needed because source prepayment and postpayment indicators are automatically measurable and bounded on a finite window (proved separately). This is the exact bridge to the original B54cp upper-strip occupation correction with its source timing conventions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB54cp_original_true_stop_upperstrip_postpaid_occ_le_prepaid_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (ω : Ω) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
        b < x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) ≤
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
        b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) := by sorry
