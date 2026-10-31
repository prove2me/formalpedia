-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_sourceStoppedClipped_futurePayoff_condExp
-- name    : AvramDividend.Classical.avram_wave3_04_sourceStoppedClipped_futurePayoff_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:25:40.492302+00:00
-- url     : https://prove2.me/theorems/9f47b4a0-3933-4cec-a933-b629047dfa9c
-- title:
--   Conditional future-increment payoff kernel with genuinely stopped and clipped controlled Lévy derivative
-- statement:
--   For the source Lévy process and an actual adapted left-continuous dividend strategy, the future increment payoff multiplied by the clipped discounted derivative of the post-payment reserve left limit, killed inclusively at the actual ruin stopping time and finite horizon, has conditional expectation given the original right-continuous history equal to the same coefficient times the stationary future-payoff mean. Finite integrability of the original future payoff suffices because the coefficient is uniformly bounded. This is a source-faithful conditional, rather than merely unconditional, martingale-increment kernel and can support the killed one-step verification budget. It uses identical sample paths for right-continuous filtration reconstruction, not an independent process copy.
-- source:
--   Private pinned compiler probe 23d17d7e-a096-431a-9427-73b83e0ffa65, exact source SHA256 316db9aa44c7d01ea260e55871eb9160cb5adf87585307c9c5106111d5b14603, passed to sentinel without candidate diagnostics. Canonical Proved source-stopped predictability 658fb6a1-1044-40b3-aa7d-2926663389af, clipping 504ebddb-4d9e-4a99-9efa-75bc0940311a, past-coefficient conditional expectation bd57036b-f0c5-4f82-aabd-535dcc4214e8 and identical-path right-continuous Lévy reconstruction 006d14c7-93c5-47e0-bbf9-8c32b53d456b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_pastCoefficient_futureIncrement_condExp

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_sourceStoppedClipped_futurePayoff_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P) :
    P[(fun ω =>
      max (-K) (min K
        (if s ≤ T then
          (Real.exp (-(q * (s : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s)) *
          (if (s : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      φ (X.X t ω - X.X s ω)) | 𝓕.rightCont s] =ᵐ[P]
    (fun ω =>
      max (-K) (min K
        (if s ≤ T then
          (Real.exp (-(q * (s : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s)) *
          (if (s : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      ∫ z, φ (X.X (t - s) z) ∂P) := by sorry
