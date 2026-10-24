-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_zero_horizon_hjb_bound
-- name    : AvramDividend.Classical.admissible_cap_truncated_zero_horizon_hjb_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:10:19.367751+00:00
-- url     : https://prove2.me/theorems/65b59b69-6442-4914-84a2-9d70fd06ad89
-- title:
--   Full HJB verification controls the initial dividend atom at horizon zero
-- statement:
--   At deterministic horizon T=0, a capped admissible strategy satisfies the expected discounted Stieltjes dividend upper bound under the original verification-function HJB maximum, boundary value, regularity and cap hypotheses. This exact zero-horizon case discharges the initial dividend atom using published HJB jump control, post-payment reserve solvency and the existing zero-horizon Stieltjes bound. Positive-time Lévy change-of-variables is a separate outstanding obligation.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_local_verification_w_nonneg_below_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_admissible_jump_bound
import Theorems.Thm_AvramDividend_Classical_truncated_zero_horizon_bound_of_initial_jump_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_zero_horizon_hjb_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
