-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_boundedPast_centeredFuture_condExp_zero
-- name    : AvramDividend.Classical.avram_wave3_04_boundedPast_centeredFuture_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:35:38.837406+00:00
-- url     : https://prove2.me/theorems/da70c95d-9460-4791-891f-3f6ec63ba110
-- title:
--   The true Lévy centred future increment multiplied by any bounded past coefficient has zero conditional mean
-- statement:
--   For original Lévy increments and an arbitrary real coefficient H measurable in the genuine time-s history F_s, assume H is uniformly bounded and the measurable stationary future increment payoff is integrable and centred. Its conditional expectation after multiplication by H is almost surely zero. The proof derives both increment and product integrability from stationarity and boundedness, then specialises the accepted original-law past-coefficient conditional expectation factorisation. This upgrades the accepted scalar mean-zero identity to a genuine martingale-difference conditional identity.
-- source:
--   Source work/avram_wave3_04_boundedPastCenteredFuture_condExpZero_20261030_v1.lean, SHA-256 e4d0fdf7532fa7e177db11c796fe48fae4c21f6132b70445f77560f4bb657e60. Remote private pinned compiler job 5ed6ef0a-c395-4fc3-a9a6-c75213886e03. Accepted original source conditional factorisation UUID bd57036b-f0c5-4f82-aabd-535dcc4214e8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_pastCoefficient_futureIncrement_condExp

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_boundedPast_centeredFuture_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (K : ℝ) (hBound : ∀ ω, ‖H ω‖ ≤ K)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P)
    (hmean : (∫ ω, φ (X.X (t - s) ω) ∂P) = 0) :
    P[(fun ω => H ω * φ (X.X t ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by sorry
