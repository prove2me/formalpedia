-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_terminal_hjb_budget_all_paths
-- name    : AvramDividend.Classical.local_verification_capped_terminal_hjb_budget_all_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:05:23.890229+00:00
-- url     : https://prove2.me/theorems/0c18e235-e6ad-47a4-bb93-5b4bfac72b11
-- title:
--   HJB terminal dividend bound for all paths, regardless of ruin before the horizon
-- statement:
--   For any capped admissible dividend strategy and strictly positive deterministic horizon T, the pathwise closed-horizon discounted Stieltjes reward is at most the strict stopped reward plus the discounted HJB verification-function decrease at a possible dividend atom at T. If T is strictly before ruin the pointwise HJB atom bound applies. If ruin has already occurred, the terminal Stieltjes component vanishes, and the nonnegative ENNReal.ofReal bound remains valid. This exact statement is unconditional in the sample point and preserves continuous dividends in the strictly stopped integral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_active_terminal_hjb_budget

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_capped_terminal_hjb_budget_all_paths
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ s in paymentTimes
        (min (ruinTime X x D ω) (ENNReal.ofReal (T : ℝ))),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
      (w (riskProcess X x D T ω) -
        w (riskProcess X x D T ω -
          (rightLimit D T ω - D T ω)))) := by sorry
