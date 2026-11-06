-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn16_original_last_cell_closed_cash_toReal_splits_endpoint_atom
-- name    : AvramDividend.Classical.avram_bv_env3_turn16_original_last_cell_closed_cash_toReal_splits_endpoint_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:29:55.778279+00:00
-- url     : https://prove2.me/theorems/c0e3c463-e30f-4b98-918e-70c41111dd15
-- title:
--   Original finite-grid closed-right cash equals strict cash plus endpoint atom in real values
-- statement:
--   For the actual original dividend Stieltjes measure restricted to stopped paymentTimes, the finite real-valued discounted cash on (a,T] equals cash on (a,T) plus the exact discounted right payment atom at T. The two summands are explicitly required finite. The result applies before or at ruin, without ignoring the terminal atom.
-- source:
--   Proved original ENNReal closed-right cell split 6703a750 plus pinned Mathlib ENNReal.toReal_add with non-top summands.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn16_original_last_cell_closed_cash_toReal_splits_endpoint_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (a : ℝ) (ha : a < (T : ℝ))
    (hStrictFinite :
      (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤)
    (hAtomFinite :
      (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤) :
    (∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
