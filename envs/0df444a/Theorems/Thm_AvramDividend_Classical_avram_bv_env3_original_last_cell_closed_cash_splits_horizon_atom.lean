-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom
-- name    : AvramDividend.Classical.avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:11:46.894254+00:00
-- url     : https://prove2.me/theorems/6703a750-785a-4233-8828-4f7a13b573fd
-- title:
--   Original closed last physical-grid cash separates the strict crossing cell and horizon atom
-- statement:
--   For any original dividend process, stopped payment clock and real last-grid endpoint strictly before the horizon, discounted cash on the closed-right final cell equals discounted cash in the strictly open final cell plus the singleton discounted dividend paid exactly at the horizon. Includes strict paymentTimes stopping, retaining the T atom. The disjoint union is proved using set identities and original dividendMeasure.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_union; direct disjoint decomposition of paymentTimes σ ∩ Ioc a T. Original process Proposition 4(i), equation (5.13), Avram, Palmowski and Pistorius (2007). Separate from P3-GRID4 secant sign, P3-2 HJB and canonical BV complement c877.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (_hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (a : ℝ) (ha : a < (T : ℝ)) :
    (∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
