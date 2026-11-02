-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_zero_cap_chronological_stopped_terminal_nonnegative
-- name    : AvramDividend.Classical.avram_wave5_03_original_zero_cap_chronological_stopped_terminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:00:37.786205+00:00
-- url     : https://prove2.me/theorems/3896d27f-0a99-4bb7-858a-789d90fd4a55
-- title:
--   Corrected UBV zero-cap true min(T,ruin) terminal postpayment/positive-ruin book payoff is nonnegative without C>0
-- statement:
--   For the ORIGINAL spectrally negative Lévy riskProcess under genuine capped dividend strategy with C=0, choose θ=toNNReal(min(T,ruinTime)). The terminal state is the actual POSTPAYMENT x+Xθ−rightLimit Dθ for θ=0 or surviving T<ruin, and the BOOK prepayment riskProcessθ at a positive ruin instant. Using the source proved postPaymentReserve cap even at time zero and the positive-time original book cap at ruin, show ENNReal.ofReal W≤C=0, hence W≤0. With only 0≤w0 and w(y)=0 for y<0, deduce 0≤wW. No hC>0, x≥0, global payoff nonnegativity, BV/UBV smoothness, hypothetical Ito, or source independence. Directly closes the zero-cap terminal branch of the corrected UBV canonical 429e17ca, complementary to earlier f72f93f3 positive-cap theorem.
-- source:
--   Avram Palmowski Pistorius (2007), corrected UBV 429e17ca and exact stopped terminal chronology. Imports Proved capped_postPaymentReserve_ofReal_le_cap and actual admissibility positive-time cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At the true finite stop, take the post-right-payment terminal state only
    on paid clocks (including zero), otherwise the original book reserve. -/

theorem AvramDividend.Classical.avram_wave5_03_original_zero_cap_chronological_stopped_terminal_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCzero : C = 0)
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0) :
    let τ : ℝ≥0∞ := ruinTime X x D ω
    let θ : ℝ≥0 := (min (T : ℝ≥0∞) τ).toNNReal
    let W : ℝ :=
      if θ = 0 ∨ (T : ℝ≥0∞) < τ then
        x + X.X θ ω - rightLimit D θ ω
      else riskProcess X x D θ ω
    0 ≤ w W := by sorry
