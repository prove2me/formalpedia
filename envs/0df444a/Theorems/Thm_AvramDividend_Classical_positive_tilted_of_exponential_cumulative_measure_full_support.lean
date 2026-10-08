-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_tilted_of_exponential_cumulative_measure_full_support
-- name    : AvramDividend.Classical.positive_tilted_of_exponential_cumulative_measure_full_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:13:56.476973+00:00
-- url     : https://prove2.me/theorems/89b8d623-da32-4bb1-bcdd-f5d31cc1d857
-- title:
--   Tilted positivity from positive cumulative mass without a zero atom
-- statement:
--   For any positive measure with strictly positive finite cumulative mass at every x>0, an exponential cumulative representation W(x)=exp(phi x) times cumulative mass gives W(x)>0 and exponential-normalised monotonicity. An atom at zero is unnecessary, unlike an existing proved bounded-variation lemma. This is a generic terminal bridge relevant to the unbounded-variation Avram scale function.
-- source:
--   Generalisation of the Proved theorem positive_tilted_of_exponential_cumulative_measure (UUID e0ac041c-6799-42ca-8c11-9b5de793ba86).

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_tilted_of_exponential_cumulative_measure_full_support
    (β : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hfin : ∀ x : ℝ, 0 < x → β (Iic x) ≠ ⊤)
    (hmass : ∀ x : ℝ, 0 < x → 0 < β (Iic x))
    (W : ℝ → ℝ)
    (hW : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * (β (Iic x)).toReal) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by sorry
