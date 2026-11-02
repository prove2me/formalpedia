-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:34:12.07133+00:00
-- url     : https://prove2.me/theorems/4fd8c76e-b059-4033-88fd-af9cbda41f92
-- title:
--   Original UBV nonmonotone clocks stabilise exact payment domains at every countable finite horizon on one a.s. event
-- statement:
--   Given the actual source spectrally negative Levy X, admissible D, unbounded variation, an arbitrary nonmonotone sequence S whose tail-infimum tends to infinity almost surely, and any countable family of nonnegative real horizons, there exists one source P-almost-sure event on which each path and each horizon index k has some finite threshold N(ω,k) beyond which all ruin-clipped S_n payment domains through that horizon exactly equal the original ruin-time domain. This is the countable intersection of the already Proved single-horizon theorem, retaining zero and infinite ruin and time zero. The threshold may depend on the horizon, and no uniform threshold, stochastic integration, dividend Stieltjes or boundary smoothness is asserted.
-- source:
--   Accepted original eventual exact payment-domain stabilisation 68f10cb0-bd2a-41c7-92bf-4bafb77cd02f; Mathlib ae_all_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤)
    (horizons : ℕ → ℝ)
    (hT : ∀ k : ℕ, 0 ≤ horizons k) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩
        Iic (horizons k) =
      paymentTimes (ruinTime X x D ω) ∩ Iic (horizons k) := by sorry
