-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:57:33.241205+00:00
-- url     : https://prove2.me/theorems/dd12ff75-5f4c-4665-ac9d-e2d261ac4b8f
-- title:
--   Actual original source stopped postpayment or ruin terminal reserve is at most the finite admissibility cap
-- statement:
--   For every outcome ω, at the true original stopped terminal state W, whether the clock is zero, strictly before ruin, or at ruin, W≤c for a finite cap c. This uses the accepted original realcap source invariant riskProcess≤c and the original monotone dividend strategy inequality D≤rightLimit D, which makes the postpayment reserve no larger than the source prepayment riskProcess. No stochastic expectation or additional probabilistic hypothesis is needed.
-- source:
--   Accepted P4-E original finite realcap invariant e8d7059c-8465-4eac-b887-63341a61ca73 and dividendStrategy_le_rightLimit 953f0e91-72ae-4c9a-bc17-de52a6c87b52; canonical stopped W branch in 0dda1be7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_realcap_invariant_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω ≤ c := by sorry
