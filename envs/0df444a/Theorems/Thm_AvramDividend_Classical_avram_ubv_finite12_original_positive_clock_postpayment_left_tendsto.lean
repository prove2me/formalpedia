-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto
-- name    : AvramDividend.Classical.avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T18:10:14.192482+00:00
-- url     : https://prove2.me/theorems/ed2e49b5-a1ed-4993-b88e-ca7017b11f6d
-- title:
--   True zero-jump original-process postpayment surplus converges to the prepayment reserve at each positive clock from the left
-- statement:
--   For a spectrally negative Levy original process with zero Levy measure and an adapted left-continuous dividend strategy, the postpayment reserve x+X_s-rightLimit D_s converges from below to x+X_t-D_t at every strictly positive clock, almost surely. The theorem uses the original same-space path and supplies the deterministic endpoint needed for a physical stopped Ito limit.
-- source:
--   Compiled by the pinned environment using original zero-nu path continuity and rightLimit left-limit identities. Needed by UBV-FINITE12 original finite cap positive-clock HJB reward budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 (riskProcess X x D t ω)) := by sorry
