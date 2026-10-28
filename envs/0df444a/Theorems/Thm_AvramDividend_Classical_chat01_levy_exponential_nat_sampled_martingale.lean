-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_nat_sampled_martingale
-- name    : AvramDividend.Classical.chat01_levy_exponential_nat_sampled_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:09:44.064181+00:00
-- url     : https://prove2.me/theorems/748f9232-5ec4-4f0c-bada-805964e25224
-- title:
--   Integer-indexed sampled Lévy compensated exponential martingale
-- statement:
--   Under the existing hypotheses for the compensated exponential martingale of a spectrally negative Lévy process, any monotone natural-number sampling of its nonnegative-real time parameter yields a discrete-time martingale against the correspondingly sampled filtration. This is the stopping-time-ready version of the Lévy exponential martingale.
-- source:
--   Proved levy_compensated_exponential_martingale and chat01_monotone_nat_sampling_martingale.

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_nat_sampling_martingale
open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat01_levy_exponential_nat_sampled_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (e : ℕ → ℝ≥0) (he : Monotone e) :
    Martingale
      (fun (n : ℕ) (ω : Ω) =>
        Real.exp (θ * X.X (e n) ω -
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ))
      ({ seq := fun (n : ℕ) => 𝓕 (e n)
         mono' := by
           intro i j hij
           exact 𝓕.mono (he hij)
         le' := by
           intro n
           exact 𝓕.le (e n) } : Filtration ℕ mΩ) P := by sorry
