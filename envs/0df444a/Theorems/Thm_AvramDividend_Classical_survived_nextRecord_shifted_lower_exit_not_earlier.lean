-- Prove2me | Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_lower_exit_not_earlier
-- name    : AvramDividend.Classical.survived_nextRecord_shifted_lower_exit_not_earlier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:12:07.38372+00:00
-- url     : https://prove2.me/theorems/df48d118-f970-46a1-935c-3822ab1fac3c
-- title:
--   Surviving a new record forces the shifted lower-exit clock after its record delay
-- statement:
--   If the original barrier process survives to a higher record v and the shift from the preceding record u is δ, then its shifted ordinary first downcrossing time below -a is no earlier than δ. This converts the previously proved pointwise shifted lower-barrier guard into a stopping-time inequality, permitting comparison of killed record discounts with two-sided exit discounts in the stopped-renewal upper argument.
-- source:
--   For each shifted time s that violates the lower boundary, use the proved survival path guard to exclude s<δ; the iInf of all such s is therefore at least δ.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_path_lower_guard

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.survived_nextRecord_shifted_lower_exit_not_earlier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + ε < X.X r ω), (r : ℝ≥0∞)))
    (hδ : u + δ = v)
    (hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω) :
    (δ : ℝ≥0∞) ≤
      (⨅ (s : ℝ≥0)
        (_ : X.X (u + s) ω - X.X u ω < -a), (s : ℝ≥0∞)) := by sorry
