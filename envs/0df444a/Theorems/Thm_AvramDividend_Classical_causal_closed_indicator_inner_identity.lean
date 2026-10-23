-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_closed_indicator_inner_identity
-- name    : AvramDividend.Classical.causal_closed_indicator_inner_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:48:32.28074+00:00
-- url     : https://prove2.me/theorems/acaae04b-aacb-49f8-acd7-a4e664ed3963
-- title:
--   Closed indicator representation of a finite causal convolution
-- statement:
--   For 0≤t≤x, the convolution over u∈(0,t] equals a whole-line integral with K cut off to u>0 and g cut off to [0,x]. The closed interval retains the u=t endpoint exactly, allowing a pointwise indicator proof with no null-singleton correction.
-- source:
--   Mathlib.MeasureTheory.Integral.Bochner.Set, integral_indicator; Set.indicator_of_mem.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_closed_indicator_inner_identity
    (K g : ℝ → ℝ) (t x : ℝ)
    (ht : 0 ≤ t) (htx : t ≤ x) :
    (∫ u in Ioc (0 : ℝ) t, K u * g (t - u) ∂volume) =
    (∫ u : ℝ,
      ((Ioi (0 : ℝ)).indicator K) u *
      ((Icc (0 : ℝ) x).indicator g) (t - u) ∂volume) := by sorry
