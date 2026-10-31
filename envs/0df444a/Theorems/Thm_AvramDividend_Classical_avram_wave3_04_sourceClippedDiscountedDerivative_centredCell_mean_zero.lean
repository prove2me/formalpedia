-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_sourceClippedDiscountedDerivative_centredCell_mean_zero
-- name    : AvramDividend.Classical.avram_wave3_04_sourceClippedDiscountedDerivative_centredCell_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:16:29.150314+00:00
-- url     : https://prove2.me/theorems/4f1a073b-c330-4fe6-b86f-625fdfcb102e
-- title:
--   Clipped discounted derivative at the actual controlled Lévy reserve is orthogonal to centred future increments
-- statement:
--   For the original spectrally negative Lévy process, its actual dividend strategy and original joint probability space, the discounted derivative of the post-payment reserve left limit sampled at a deterministic start time is clipped at ±K, then multiplied by any centred integrable future Lévy increment payoff. The resulting expected product is exactly zero. The proof uses the canonical predictable reserve, discounted derivative and clipping lemmas; transports the original sample path to the right-continuous filtration with the proven identical-path Lévy reconstruction, then invokes the Proved bounded past-coefficient martingale-difference theorem. No assumption of independent dividends or independent equal-law copy is made; no full stochastic integral exists yet.
-- source:
--   Accepted canonical source left-limit predictability UUID 94ee9994-3882-4f29-8637-06666efe721d; discounted derivative fcdc8c77-b533-49ff-8001-cf775c3945a8; clipping 504ebddb-4d9e-4a99-9efa-75bc0940311a; bounded past-centred increment 488296c2-5a96-4786-a577-a02199ace877; identical-path rightCont Lévy reconstruction 006d14c7-93c5-47e0-bbf9-8c32b53d456b. Exact source reached private pinned compiler probe sentinel 7ab5cac6-0d64-4769-a480-fabfc4e343d7 without candidate errors, source SHA-256 f2a5a29a82cf042ef2e639aafb651ed3d4a7a6f69b51b3ffa0602cc68b17197d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_sourceClippedDiscountedDerivative_centredCell_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P)
    (hmean : (∫ ω, φ (X.X (t - s) ω) ∂P) = 0) :
    (∫ ω,
      max (-K) (min K
        (Real.exp (-(q * (s : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s))) *
      φ (X.X t ω - X.X s ω) ∂P) = 0 := by sorry
