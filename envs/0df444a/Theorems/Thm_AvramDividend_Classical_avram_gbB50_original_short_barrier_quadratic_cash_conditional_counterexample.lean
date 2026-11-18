-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB50_original_short_barrier_quadratic_cash_conditional_counterexample
-- name    : AvramDividend.Classical.avram_gbB50_original_short_barrier_quadratic_cash_conditional_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:45:51.703622+00:00
-- url     : https://prove2.me/theorems/ca185fb6-617b-4a05-9f39-45637c5fb378
-- title:
--   Original short cap barrier and true quadratic starting payoff: conditional strict cash contradiction
-- statement:
--   For the quadratic payoff w(y)=2y-4y² with exact starting value w(1/8)=3/16, a short upper-cap reflected source tube has stopping clock T and terminal reserve in [5/44,1/8]. If its exact stopped discounted cash identity holds, the fixed-band pathwise cash budget is strictly violated. The stochastic identity remains an explicit hypothesis, so this is a source-faithful conditional contradiction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB39_short_horizon_cash_identity_contradiction
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB50_original_short_barrier_quadratic_cash_conditional_counterexample
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
  (hT : 0 < T)
  (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ))
  (F N : ℝ)
  (hCash : F - (3 / 16 : ℝ) - N =
    (193419 / 968 : ℝ) * (1 - Real.exp (-(1 / 100000 : ℝ))) +
    Real.exp (-(1 / 100000 : ℝ)) *
      (riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω -
        4 * (riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω) ^ 2 -
        15 / 242) - (1 / 1936 : ℝ)) :
  sInf ((Icc (0 : ℝ≥0) T ∩
    (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
      Ici (-(5 / 44 : ℝ))) ∪ {T}) = T ∧
  ¬ F - (3 / 16 : ℝ) ≤ N + (1 / 1936 : ℝ) := by sorry
