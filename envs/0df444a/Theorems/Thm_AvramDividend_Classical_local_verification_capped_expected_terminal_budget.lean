-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_expected_terminal_budget
-- name    : AvramDividend.Classical.local_verification_capped_expected_terminal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:11:01.367073+00:00
-- url     : https://prove2.me/theorems/d03e5b3b-426f-4c88-8ba3-508e330f3f09
-- title:
--   Expected capped verification bound reduces to strictly stopped reward plus terminal HJB drop
-- statement:
--   Under the exact local HJB hypotheses for a capped admissible dividend strategy and any positive deterministic T, the expected actual closed-horizon discounted Lebesgue–Stieltjes dividend reward is bounded by the expectation of the strictly stopped payoff plus the discounted candidate-value decrease from the possible terminal dividend jump. The pathwise all-path HJB endpoint estimate, including trajectories ruined before T, is integrated by monotonicity of the nonnegative lower integral. The unproved stochastic obligation is an upper bound on the latter expectation by w(x).

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_terminal_hjb_budget_all_paths

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_capped_expected_terminal_budget
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
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω,
      (∫⁻ s in paymentTimes
          (min (ruinTime X x D ω) (ENNReal.ofReal (T : ℝ))),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
      ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
        (w (riskProcess X x D T ω) -
          w (riskProcess X x D T ω -
            (rightLimit D T ω - D T ω)))) ∂P) := by sorry
