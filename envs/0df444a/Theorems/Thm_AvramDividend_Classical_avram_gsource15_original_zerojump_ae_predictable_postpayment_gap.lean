-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gsource15_original_zerojump_ae_predictable_postpayment_gap
-- name    : AvramDividend.Classical.avram_gsource15_original_zerojump_ae_predictable_postpayment_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:47:46.460243+00:00
-- url     : https://prove2.me/theorems/50ea6a60-9246-4b29-a906-83e6a4d89282
-- title:
--   Zero-jump original-filtration predictable-to-postpayment frozen source atom correction
-- statement:
--   For the original Levy process with zero jump measure, almost surely simultaneously at every strictly positive time, the left-limit frozen Gaussian source reserve is its current postpayment value plus the original dividend strategy's right-hand payment atom. Uses the already Proved global path continuity under nu=0 and exact postpayment left limit; no auxiliary Brownian or missing Ito conclusion is imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gsource15_original_zerojump_ae_predictable_postpayment_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        (x + X.X t ω - rightLimit D t ω) +
          (rightLimit D t ω - D t ω) := by
  sorry
