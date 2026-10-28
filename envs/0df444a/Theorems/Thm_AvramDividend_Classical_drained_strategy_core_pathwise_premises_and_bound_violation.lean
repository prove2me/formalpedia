-- Prove2me | Theorems.Thm_AvramDividend_Classical_drained_strategy_core_pathwise_premises_and_bound_violation
-- name    : AvramDividend.Classical.drained_strategy_core_pathwise_premises_and_bound_violation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:42:27.034751+00:00
-- url     : https://prove2.me/theorems/9d21e277-1af0-4e10-8404-edde635085f6
-- title:
--   Instantly ruined drained barrier strategy satisfies all core pathwise premises but violates the nonpositive claimed payout bound
-- statement:
--   For any spectrally negative Lévy process, any positive initial reserve, and any verification function agreeing with y−1 on nonnegative reserves whose value at the initial reserve is nonpositive, the barrier-zero plus unit-rate drain is an admissible strategy under the infinite cap, its stopped nonnegativity hypothesis is vacuous due to immediate ruin, and its dividend jumps satisfy the candidate drop inequality. Yet its positive initial dividend makes the canonical proposed nonpositive expected-reward upper bound false at every nonnegative horizon. This unifies the strategy side of the missing-boundary-assumption audit, conditional only on the existence of a model satisfying the analytical premises.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i) and the established Prove2Me drained-strategy boundary lemmas.

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_admissible_infinite_cap
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_ruinTime_zero
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_affine_jump_control
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_no_nonpositive_expected_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.drained_strategy_core_pathwise_premises_and_bound_violation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 < x)
    (w : ℝ → ℝ) (hw_affine : ∀ y, 0 ≤ y → w y = y - 1)
    (hwx : w x ≤ 0) (q T : ℝ) (hT : 0 ≤ T) :
    let D : ℝ≥0 → Ω → ℝ :=
      fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
    IsAdmissibleLe X x ⊤ D ∧
    (∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) ∧
    ¬ ((∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) := by sorry
