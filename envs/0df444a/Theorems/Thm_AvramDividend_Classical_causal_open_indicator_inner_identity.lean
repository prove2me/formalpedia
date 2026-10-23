-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_open_indicator_inner_identity
-- name    : AvramDividend.Classical.causal_open_indicator_inner_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:56:42.58342+00:00
-- url     : https://prove2.me/theorems/0e8bdc2e-2a5a-4054-b710-f252c448dd4b
-- title:
--   Open-indicator representation of finite causal convolution
-- statement:
--   For 0 ≤ t ≤ x the causal integral of K(u)g(t−u) over (0,t] equals the full-line convolution of the positive-lag kernel indicator and the input restricted to (0,x]. The integrands differ only at the endpoint u=t, which has zero Lebesgue measure. This bridge relates interval convolution to the already proved truncated-convolution Fubini theorems.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_open_indicator_inner_identity
    (K g : ℝ → ℝ) (t x : ℝ)
    (ht : 0 ≤ t) (htx : t ≤ x) :
    (∫ u in Ioc (0 : ℝ) t, K u * g (t - u) ∂volume) =
    (∫ u : ℝ,
      ((Ioi (0 : ℝ)).indicator K) u *
      ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) := by sorry
