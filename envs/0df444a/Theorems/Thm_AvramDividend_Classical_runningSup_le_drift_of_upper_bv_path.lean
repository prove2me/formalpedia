-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_le_drift_of_upper_bv_path
-- name    : AvramDividend.Classical.runningSup_le_drift_of_upper_bv_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:23:36.562263+00:00
-- url     : https://prove2.me/theorems/d73bfb97-6c33-4764-9268-bcf84a49ae7f
-- title:
--   The actual running supremum stays below the positive drift upper envelope
-- statement:
--   A deterministic upper-envelope theorem for the actual Lévy running supremum. If X_u≤d u at every time up to t and d≥0, then the raw path supremum and hence S_t are bounded by d t. Uses the Proved runningSup_eq_rawSup_nonneg identity and bounded indexed supremum. This yields drawdown S_t−X_t≤d t−X_t and connects original reflected ruin to the actual nonnegative residual process.
-- source:
--   Avram Palmowski Pistorius (2007), reflected running supremum; accepted runningSup_eq_rawSup_nonneg in Prove2Me.

import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_le_drift_of_upper_bv_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (hDrift : 0 ≤ X.drift)
    (hPath : ∀ u : ℝ≥0, u ≤ t →
      X.X u ω ≤ X.drift * (u : ℝ)) :
    runningSup X t ω ≤ X.drift * (t : ℝ) := by sorry
