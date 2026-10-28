-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_prefix_runningSup_linear
-- name    : AvramDividend.Classical.bv_actual_residual_zero_prefix_runningSup_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:04:01.166787+00:00
-- url     : https://prove2.me/theorems/e7b046fb-50f4-4f88-86d3-2d428e4dec2f
-- title:
--   Actual bounded-variation zero-residual survival prefix has exactly linear running supremum
-- statement:
--   Under the original Avram standing assumptions and bounded variation, a zero residual history d s-X_s=0 throughout the continuous interval [0,t] implies that the actual Lévy running supremum follows the drift line S_u=d u at every u≤t. Use the Proved positive-drift standing lemma and the Proved exact runningSup linear-prefix theorem. This is the direct bridge from the exponential no-jump survival event to the original Stieltjes running-record reward.
-- source:
--   Proved bv_standing_drift_pos, runningSup_linear_of_linear_capital_prefix; Avram Palmowski Pistorius (2007), first-jump zero-barrier dividend identity.

import Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_residual_zero_prefix_runningSup_linear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (ω : Ω) (t : ℝ≥0)
    (hHistory : ∀ s : ℝ≥0, s ≤ t →
      (s : ℝ) * X.drift - X.X s ω = 0) :
    ∀ u : ℝ≥0, u ≤ t →
      runningSup X u ω = X.drift * (u : ℝ) := by sorry
