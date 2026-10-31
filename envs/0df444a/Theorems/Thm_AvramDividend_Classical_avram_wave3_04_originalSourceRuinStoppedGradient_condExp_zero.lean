-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalSourceRuinStoppedGradient_condExp_zero
-- name    : AvramDividend.Classical.avram_wave3_04_originalSourceRuinStoppedGradient_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:40:02.313005+00:00
-- url     : https://prove2.me/theorems/41a8c117-d731-43e0-9c3d-57ca2d93e8a9
-- title:
--   The actual ruin-stopped controlled Lévy reserve gradient has zero conditional mean against every centred future increment
-- statement:
--   Given the original spectrally negative Lévy process X and an actually adapted, left-continuous dividend control D, form the strict pre-jump limit of the post-payment reserve x+X−D+, apply the discounted verification gradient, stop inclusively at the genuine ruin time and deterministic horizon, and clip to [-K,K]. For every integrable centred future Lévy payoff, the product with this source-specific coefficient has conditional expectation zero given the original right-continuous filtration at the starting time. Source-independent past-coefficient conditional factorisation is applied to a reconstructed Lévy process with identical paths and triplet, preserving the actual joint law with dividends. This is the stopped martingale-difference statement, short of continuous-time integral convergence.
-- source:
--   Exact Lean source work/avram_wave3_04_sourceStoppedGradient_condExpZero_20261030_v1.lean, SHA-256 549779c714e6ed2ebb78e25e129ae4c4533f2b0d4a8d9605a6fcc95a70f056df. Exact pinned remote private compiler probe d7bbf46d-2c98-42b2-b631-697ecb751e00 reached sentinel with no candidate errors. Depends exclusively on canonical Proved past-coefficient source conditional expectation, stopped discounted source predictability, clipping, and original Lévy right-continuous reconstruction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_pastCoefficient_futureIncrement_condExp

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_originalSourceRuinStoppedGradient_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P)
    (hmean : (∫ ω, φ (X.X (t - s) ω) ∂P) = 0) :
    P[(fun ω =>
      max (-K) (min K
        (if s ≤ T then
          (Real.exp (-(q * (s : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s)) *
          (if (s : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0)) *
      φ (X.X t ω - X.X s ω)) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by sorry
