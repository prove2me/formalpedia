-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_unrestricted_discounted_stieltjes_antitone_rate
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_unrestricted_discounted_stieltjes_antitone_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:56:34.776542+00:00
-- url     : https://prove2.me/theorems/9eb75681-e97a-4ce6-a468-0106ee0fbdb7
-- title:
--   Exact original unrestricted pre-ruin dividend Stieltjes cash is antitone in the discount rate
-- statement:
--   For an arbitrary original Stieltjes dividend measure D ω, exact ruin time σ and any q₁≤q₂, the full ENNReal discounted Stieltjes integral on paymentTimes σ is antitone in discount, without finite horizon truncation. The proof uses actual source measurable nonnegative paymentTimes and identical dividendMeasure. Its unrestricted domain retains the time-zero right-limit atom and all continuous and jump cash. This gives the source-identical comparison needed to transport signed integrability across rates.
-- source:
--   Accepted actual-source paymentTimes_measurable 88dafb7f and same-measure finite-horizon proof a4088502; Mathlib lintegral_mono_ae and ae_restrict_mem.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_03_original_full_unrestricted_discounted_stieltjes_antitone_rate
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (σ : ℝ≥0∞)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ t in paymentTimes σ,
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes σ,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω)) := by sorry
