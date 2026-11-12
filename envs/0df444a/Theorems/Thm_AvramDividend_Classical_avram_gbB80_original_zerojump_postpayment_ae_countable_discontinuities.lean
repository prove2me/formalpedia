-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
-- name    : AvramDividend.Classical.avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:29:45.959658+00:00
-- url     : https://prove2.me/theorems/91d23553-0a8d-4944-b2f8-7790fe74f2ad
-- title:
--   Original zero-jump Levy postpayment reserve discontinuity times countable almost surely
-- statement:
--   For the unchanged original Gaussian zero-jump spectrally negative Levy process X, probability P, original admissible dividend D and filtration, the original postpayment reserve x + X.X t omega - rightLimit D t omega has only countably many discontinuity times P-almost surely. This combines previously authoritative original zero-jump path continuity b462a147 and source-specific original reserve continuity B79, and is needed to handle time-grid left sampling in the original B61 Gaussian two-grid coefficient energy convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_gbB79_original_postpayment_reserve_discontinuities_countable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) :
    ∀ᵐ ω ∂P,
      Set.Countable {t : ℝ≥0 |
        ¬ ContinuousAt (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t} := by sorry
