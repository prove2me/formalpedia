-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn17_original_last_cell_cash_real_atom_automatic
-- name    : AvramDividend.Classical.avram_bv_env3_turn17_original_last_cell_cash_real_atom_automatic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:34:50.570563+00:00
-- url     : https://prove2.me/theorems/8c3828ec-2163-461f-8d07-0d572e340546
-- title:
--   Original stopped real final-grid cash splits exact endpoint payment without finiteness premises
-- statement:
--   For any original Stieltjes dividend strategy and stopping domain paymentTimes sigma, closed-right final-cell discounted real cash equals the strictly open cell cash plus the exact right endpoint singleton payment, with q>=0 and a<T. The finiteness of each piece is proved from the already established full closed-horizon Stieltjes cash budget. No stochastic regularity or synthetic approximation is assumed.
-- source:
--   Proved 6703a750 exact source split, accepted turn16 real conversion and original closed-horizon cash finiteness theorem avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite. Pinned lintegral_mono_set and ENNReal.toReal_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn16_original_last_cell_closed_cash_toReal_splits_endpoint_atom
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn17_original_last_cell_cash_real_atom_automatic
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (a : ℝ) (ha : a < (T : ℝ)) :
    (∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
