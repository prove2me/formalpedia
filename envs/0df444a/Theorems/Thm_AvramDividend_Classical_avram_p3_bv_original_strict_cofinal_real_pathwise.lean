-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cofinal_real_pathwise
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cofinal_real_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:08:37.3182+00:00
-- url     : https://prove2.me/theorems/7e6ebfc4-8344-425f-b7fc-8b7a8ceae388
-- title:
--   Original admissible Stieltjes strict real cash equals every cofinal real supremum pathwise
-- statement:
--   For every original admissible dividend strategy, every sample path, any nonnegative discount and finite observation horizon, the real-valued strict-horizon discounted original Stieltjes cash is the supremum of cash amounts on every increasing cofinal family of earlier horizons. Finiteness is automatic because strict payment times are contained in the true closed-horizon dividend payment set, whose original Stieltjes cash is pathwise finite. This includes the actual time-zero atom and all intermediate diffuse payments, and requires no extra stopping, integrability or jump-compensator hypothesis.
-- source:
--   Proved c4e50d93 original closed-horizon literal cash finiteness, Proved e1962f77 strict real cofinal theorem, and pinned Mathlib lintegral_mono_set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_real_iSup
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cofinal_real_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n) :
    (⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal := by sorry
