-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_eventual_payment_domain_stabilises
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_eventual_payment_domain_stabilises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:13:29.601188+00:00
-- url     : https://prove2.me/theorems/68f10cb0-bd2a-41c7-92bf-4bafb77cd02f
-- title:
--   Original UBV nonmonotone clocks have eventually exact finite-horizon ruin payment domains almost surely
-- statement:
--   For the actual original spectrally negative Levy process X and admissible strategy D, under the original unbounded-variation hypothesis and an arbitrary sequence of extended nonnegative stochastic clocks S whose tail-infimum tends to infinity almost surely, at every fixed finite nonnegative horizon T there is an almost-sure event on which each path admits its own N such that all later ruin-clipped payment-time domains through T equal the full ruin-time domain exactly. Includes zero ruin, infinite ruin and the payment time 0. No monotonicity or stopping-time status of S, zero-boundary smoothness, Stieltjes decomposition or controlled Ito-Meyer assumption is introduced.
-- source:
--   Accepted original pathwise exact finite-horizon payment-domain theorem e0a34e97-9144-43ea-a506-3de6e7680e0c; corrected core 429e17ca-5528-40b5-b593-7c03973d0706; source paymentTimes and ruinTime definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_eventual_payment_domain_stabilises
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T =
        paymentTimes (ruinTime X x D ω) ∩ Iic T := by sorry
