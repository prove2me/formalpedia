-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
-- name    : AvramDividend.Classical.avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:19:46.738624+00:00
-- url     : https://prove2.me/theorems/89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d
-- title:
--   Original chronological predictable left reserve equals the genuine pre-payment reserve at every atomless nonnegative-time clock almost everywhere
-- statement:
--   For the actual original Levy source X and any same-filtration nondecreasing adapted dividend path D, the chronological predictable pre-event reserve, the strict left limit of x+X−D_right, equals the genuine current pre-payment book reserve x+X−D at almost every positive time for any atomless measure directly on NNReal time, on P-a.e. original sample path. The lemma does not require unbounded variation and does not assume dividend measures are atomless. It is the exact source chronology bridge needed to transfer the UBV cap-contact physical-time occupation and HJB generator estimates to the predictable pre-jump argument. Positive-time zero atom avoids special initial right-payment cases.
-- source:
--   Accepted original all-BV/UBV postpayment countable-jump atomless continuity 2c5e035b-c9bf-4b4b-b635-3029428f3945 and actual right-dividend-jump countability 9044d9ad-758f-4608-91af-f6ff216b7b36. Direct NNReal-time interface for corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706. Does not attempt full controlled chain rule or Stieltjes correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_atomless_continuity
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ν : Measure ℝ≥0) [NullSingletonClass ν] :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂ν, 0 < t →
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        riskProcess X x D t ω := by sorry
