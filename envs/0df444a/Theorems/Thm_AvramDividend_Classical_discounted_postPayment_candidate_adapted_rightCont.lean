-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_adapted_rightCont
-- name    : AvramDividend.Classical.discounted_postPayment_candidate_adapted_rightCont
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T08:56:32.34123+00:00
-- url     : https://prove2.me/theorems/0db0f8d0-f6c4-443b-a194-4b49912cb395
-- title:
--   The discounted post-payment HJB candidate is adapted to the right-continuous filtration
-- statement:
--   For a continuous-on-nonnegative candidate w vanishing on negative reserves, a spectrally negative Lévy process and adapted monotone dividend strategy, the process Y_t=exp(-qt)w(x+X_t−D_{t+}) is adapted to the right-continuous filtration for every real q. By the already Proved Borel candidate/post-payment adaptedness theorem, w(U_t+) is F.rightCont(t)-measurable. The multiplier exp(-qt) is deterministic at each time, so multiplying by a measurable constant preserves filtration measurability. This direct adaptedness theorem is useful for stopped and conditional-expectation calculations. It does not assume the unavailable stochastic Itô identity.
-- source:
--   Uses Proved local_verification_candidate_borel_and_postPayment_adapted (candidate 12220) and measurable_const.mul; no Open import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_postPayment_candidate_adapted_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) :
    Adapted 𝓕.rightCont
      (fun t ω => Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)) := by sorry
