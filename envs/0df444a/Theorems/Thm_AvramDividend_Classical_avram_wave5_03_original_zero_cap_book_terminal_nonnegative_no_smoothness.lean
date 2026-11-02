-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_zero_cap_book_terminal_nonnegative_no_smoothness
-- name    : AvramDividend.Classical.avram_wave5_03_original_zero_cap_book_terminal_nonnegative_no_smoothness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:58:14.295041+00:00
-- url     : https://prove2.me/theorems/24c32234-92d7-42a6-913c-5507136c39ae
-- title:
--   Corrected UBV zero-cap actual original prepayment reserve terminal payoff is nonnegative without positive cap or smoothness
-- statement:
--   For the ORIGINAL capped SpectrallyNegativeLevy riskProcess with C=0 (the corrected UBV canonical core does not require C>0), the actual prepayment reserve at every sample time, INCLUDING t=0 and a positive ruin instant, is necessarily nonpositive by the source admissibility cap and exact X.X_zero,D0=0 conventions. Thus w(riskProcess)≥0 using only 0≤w0 and w=0 on the strictly negative halfline, without global w positivity, BV/UBV smoothness or a positive cap. This handles the zero-cap book terminal branch which the earlier hC>0 terminal lemma cannot apply to.
-- source:
--   Avram Palmowski Pistorius (2007) corrected UBV stochastic core 429e17ca and original riskProcess/IsAdmissibleLe; hD.2 positive-time cap and hD.1.1 source D0=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_zero_cap_book_terminal_nonnegative_no_smoothness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCzero : C = 0)
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (riskProcess X x D t ω) := by sorry
