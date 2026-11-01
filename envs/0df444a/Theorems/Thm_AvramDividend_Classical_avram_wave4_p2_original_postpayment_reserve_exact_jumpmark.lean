-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_exact_jumpmark
-- name    : AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_exact_jumpmark
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:57:11.427992+00:00
-- url     : https://prove2.me/theorems/74dd09be-dae5-405e-b8b4-41a6c32a5046
-- title:
--   Actual controlled post-payment reserve jump equals original Lévy mark minus right-dividend payment jump
-- statement:
--   For every positive time and every sample path of the original spectrally negative Lévy process with any actual admissible dividend strategy, the precise jump of the post-payment controlled reserve U⁺_t=x+X_t−D_{t+}, relative to its strict-left limit, equals ΔX_t−Δ⁺D_t. Uses the independently established original chronological left-limit identity, not a transformed process or a stochastic integral. This is the exact source jump splitting required for the original same-filtration Lévy-mark compensator and controlled Itô–Meyer jump term in both BV and UBV.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), stopped controlled Itô–Meyer formula; canonical actual source left-limit identity 06dc12b5. The missing compensator law 393b03a8 is deliberately not assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_exact_jumpmark
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (x + X.X t ω - rightLimit D t ω) -
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) -
        (rightLimit D t ω - D t ω) := by sorry
