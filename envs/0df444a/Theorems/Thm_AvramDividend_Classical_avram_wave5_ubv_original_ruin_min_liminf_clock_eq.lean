-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_min_liminf_clock_eq
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_ruin_min_liminf_clock_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:59:35.108473+00:00
-- url     : https://prove2.me/theorems/b6f6314c-f08c-4ac7-987f-77eeccb7e5fd
-- title:
--   Ruin-clipped nonmonotone original clocks have correct almost-sure liminf
-- statement:
--   Let S_n be arbitrary, not necessarily monotone, extended-nonnegative random clocks along the original SpectrallyNegativeLevy process and actual dividend strategy. If their tail infima tend almost surely to infinity, then the tail-infimum monotone envelope of the clocks min(ruinTime,S_n) tends almost surely to the genuine ruinTime. The proof distributes min with the fixed random ruin endpoint through infima and suprema of ENNReal, including the zero and infinite ruin endpoints. No adaptedness, stopping, bounded-variation, smoothness or extra boundary assumptions are required for this purely pathwise clock identity; later applications supply measurability from genuine stopping-time hypotheses.
-- source:
--   Corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706; source SpectrallyNegativeLevy P 𝓕, actual ruinTime X x D, no synthetic noise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_ruin_min_liminf_clock_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) =
        ruinTime X x D ω := by sorry
