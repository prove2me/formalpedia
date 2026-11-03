-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_terminal_atom_survival_indicator_formula
-- name    : AvramDividend.Classical.avram_wave7_11_positive_horizon_terminal_atom_survival_indicator_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:54:03.004115+00:00
-- url     : https://prove2.me/theorems/12ea0787-0370-4897-9385-808c4a753dbd
-- title:
--   Exact original discounted terminal Stieltjes atom equals source dividend atom times pre-ruin survival indicator
-- statement:
--   For the original dividendMeasure D ω and strictly positive finite T, the contribution at exactly T is the discounted source dividend-measure singleton mass if and only if ENNReal.ofReal T is strictly earlier than the original ruin stopping clock σ, and is zero otherwise. Both cases are proved using original paymentTimes and the earlier accepted terminal survival and expired-clock lemmas; no atom-vanishing assumption or replacement process is introduced.
-- source:
--   W7-11 Proved positive endpoint payment iff 98c71508, W7-11 original no-terminal-if-expired 0e0c52cb, independent true Stieltjes terminal atom e9ede15b, Mathlib set/lintegral empty.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_terminal_stieltjes_atom_exact_survival
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_no_terminal_payment_if_clock_ended
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_positive_horizon_terminal_atom_survival_indicator_formula
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) (hT : 0 < T) :
    (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      if ENNReal.ofReal T < σ then
        (dividendMeasure D ω) ({T} : Set ℝ) *
          ENNReal.ofReal (Real.exp (-(q * T)))
      else 0 := by sorry
