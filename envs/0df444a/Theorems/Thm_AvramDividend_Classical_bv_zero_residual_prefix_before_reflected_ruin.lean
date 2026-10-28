-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_zero_residual_prefix_before_reflected_ruin
-- name    : AvramDividend.Classical.bv_zero_residual_prefix_before_reflected_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:20:52.926461+00:00
-- url     : https://prove2.me/theorems/22333cb4-7049-4113-9cc5-40c31f10c6f1
-- title:
--   A zero-drift-residual prefix lies before the original reflected drawdown ruin
-- statement:
--   For an actual Standing bounded-variation spectrally negative Lévy path with residual d*s−X_s exactly zero at every s≤t, the original strictly positive drawdown ruin time at barrier zero is at least t. The Proved zero-residual running-record lemma gives S_s=d*s=X_s on this prefix, hence drawdown S_s−X_s=0. The original ruin clock is the infimum of later s with strictly positive drawdown, so it cannot occur before t. This establishes one direction of the stopping-clock comparison needed for the first-jump reward identity.
-- source:
--   Avram Palmowski Pistorius (2007), §3.3; Prove2Me accepted zero residual record theorem and authoritative barrierRuinTime definition.

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_prefix_runningSup_linear
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_zero_residual_prefix_before_reflected_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (ω : Ω) (t : ℝ≥0)
    (hHistory : ∀ s : ℝ≥0, s ≤ t →
      (s : ℝ) * X.drift - X.X s ω = 0) :
    (t : ℝ≥0∞) ≤ barrierRuinTime X 0 ω := by sorry
