-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:39:21.145277+00:00
-- url     : https://prove2.me/theorems/06839544-2429-48b2-bce8-78e4b76dd814
-- title:
--   Same-source all-cap post-payment terminal candidate remains nonnegative across UBV creeping and overshoots
-- statement:
--   For the actual SpectrallyNegativeLevy P 𝓕 and every original admissible strategy D at cap C, including zero and infinity, the verification function at the reserve immediately after a right dividend jump, namely w(x + X.X t ω − rightLimit D t ω), is nonnegative at every physical time and every path. The proof uses the previously Proved original capped post-payment reserve bound, exact all-cap C2 gradient secant closed at zero, the indispensible corrected boundary 0≤w(0), continuity on [0,∞), and w(y)=0 for y<0. It makes no bounded-variation, positive-cap, no-creeping, w(0)=0, or boundary smoothness assumption. In particular the terminal is nonnegative whether ruin occurs by continuous creeping at zero or a negative overshoot. This is an endpoint sign statement, not a dividend Stieltjes integral, jump compensation, or controlled Itô–Meyer proof.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706. Reuse Proved original postpayment upper cap 16104f4f-861a-44e4-8c74-94a125730fa3 and Proved closed allcap C2 gradient secant, same technique as accepted book-reserve terminal theorem c7bf9b3b-8066-4109-a2fc-b9ac81e3ca0f. No target or milestone changes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      0 ≤ w (x + X.X t ω - rightLimit D t ω) := by sorry
