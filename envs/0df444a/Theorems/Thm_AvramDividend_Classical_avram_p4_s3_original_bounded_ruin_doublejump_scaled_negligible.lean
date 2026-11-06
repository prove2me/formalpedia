-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_ruin_doublejump_scaled_negligible
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_ruin_doublejump_scaled_negligible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:28:11.154215+00:00
-- url     : https://prove2.me/theorems/1dad76d1-269a-49eb-98c4-41771dbdedf3
-- title:
--   Source-exact bounded-ruin multi-jump collisions vanish at the physical first-order scale
-- statement:
--   For any sample-dependent original-process clock τ_k bounded by T/k, the physical probability of two or more separated negative-band jumps is O(k^-2), so k times that probability tends to zero. This supplies the true ruin-clock double-jump negligibility required when passing finite-band stochastic terms to source Itô–Meyer drift rates.
-- source:
--   Accepted P4-S3 bounded random clock double-jump bound c9ffdee3-c16f-4ec1-a259-473f8623e9fd and exact physical horizon rate conversion c3093fe5-49b3-448a-b97e-e89c4d11ca3b; squeeze by the Lévy square-rate term.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_ruin_doublejump_scaled_negligible
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : ℕ → Ω → ℝ≥0) (hτ : ∀ k ω, τ k ω ≤ T / (k : ℝ≥0)) :
    Filter.Tendsto
      (fun k : ℕ => (k : ℝ) * P.real {ω : Ω |
        2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard})
      Filter.atTop (nhds (0 : ℝ)) := by sorry
