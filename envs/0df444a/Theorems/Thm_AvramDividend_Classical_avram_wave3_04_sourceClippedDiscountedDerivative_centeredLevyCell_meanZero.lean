-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_sourceClippedDiscountedDerivative_centeredLevyCell_meanZero
-- name    : AvramDividend.Classical.avram_wave3_04_sourceClippedDiscountedDerivative_centeredLevyCell_meanZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:53:20.270476+00:00
-- url     : https://prove2.me/theorems/035ffcf4-f52b-48fc-886a-26d3c851f72a
-- title:
--   Clipped discounted true dividend-reserve derivative is orthogonal to a centred future original Lévy increment
-- statement:
--   For the actual joint law of the original spectrally negative Lévy process X and a left-continuous adapted dividend strategy D, sample the true controlled reserve pre-jump value U+_{s−} at a deterministic past time s. Its discounted candidate derivative, clipped to the finite range [-K,K], is strongly measurable in the transported right-continuous filtration at s and uniformly bounded. The identical-path right-continuous Lévy process reconstruction allows source original future-increment independence to be applied to this coefficient. Consequently its product with any centred integrable Borel payoff φ(X_t−X_s) has expectation zero. This is a genuine same-path stochastic martingale cell identity, not merely a conditional reduction or a substitute equal-law Brownian construction.
-- source:
--   Canonical Proved source original reserve left-limit predictable UUID 94ee9994-3882-4f29-8637-06666efe721d, discounted derivative predictability fcdc8c77-b533-49ff-8001-cf775c3945a8, clipped predictable bounded 504ebddb-4d9e-4a99-9efa-75bc0940311a, bounded source future-centred product 488296c2-5a96-4786-a577-a02199ace877, and identical-path right-continuous Lévy process 006d14c7-93c5-47e0-bbf9-8c32b53d456b. Private pinned compiler job 7ab5cac6-0d64-4769-a480-fabfc4e343d7 reached sentinel with no candidate errors, source SHA-256 f2a5a29a82cf042ef2e639aafb651ed3d4a7a6f69b51b3ffa0602cc68b17197d.

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

theorem AvramDividend.Classical.avram_wave3_04_sourceClippedDiscountedDerivative_centeredLevyCell_meanZero
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
