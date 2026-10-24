-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_active_terminal_hjb_budget
-- name    : AvramDividend.Classical.local_verification_capped_active_terminal_hjb_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:50:45.177978+00:00
-- url     : https://prove2.me/theorems/8692267b-059b-4185-a402-b39ff48025b9
-- title:
--   Active terminal dividend HJB bound on the exact closed-horizon Stieltjes payoff
-- statement:
--   For a capped admissible strategy satisfying the complete original HJB smoothness and generator hypotheses, if a strictly positive deterministic time T occurs before ruin, the discounted Stieltjes reward through the closed horizon T is bounded above by the strictly stopped reward (the payment-time set of min(ruinTime,ofReal T)) plus the discounted verification-function decrement from the dividend right-jump at T. This is a pathwise, exact terminal-atom correction. It keeps the continuous dividend Stieltjes mass in the stopped reward, and makes no unsupported martingale claim.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_dividendMeasure_atom_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_capped_active_terminal_hjb_budget
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
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (hactive : (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ s in paymentTimes
        (min (ruinTime X x D ω) (ENNReal.ofReal (T : ℝ))),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
      (w (riskProcess X x D T ω) -
        w (riskProcess X x D T ω -
          (rightLimit D T ω - D T ω)))) := by sorry
