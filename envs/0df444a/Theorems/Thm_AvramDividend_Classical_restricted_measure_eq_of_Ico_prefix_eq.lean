-- Prove2me | Theorems.Thm_AvramDividend_Classical_restricted_measure_eq_of_Ico_prefix_eq
-- name    : AvramDividend.Classical.restricted_measure_eq_of_Ico_prefix_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:47:10.778404+00:00
-- url     : https://prove2.me/theorems/99647343-78f5-41c9-8648-2d46ff306c68
-- title:
--   Finite prefix interval agreement determines equality of restricted Stieltjes-type measures
-- statement:
--   Suppose two Borel measures on the real line have equal mass on all closed-open intervals with nonnegative starting endpoint and ending endpoint no later than a finite horizon T, and one measure has finite mass on [0,T). Then their restrictions to [0,T) agree on all measurable sets. This uses measure extensionality on Ico intervals and is a missing bridge from interval-by-interval dividend equality to equality of discounted Stieltjes integrals.
-- source:
--   Pinned Mathlib measure extensionality on Ico intervals; stochastic dividend verification under Avram–Palmowski–Pistorius (2007).

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.restricted_measure_eq_of_Ico_prefix_eq
    (μ ν : Measure ℝ) (T : ℝ)
    (hfin : μ (Ico 0 T) < ⊤)
    (heq : ∀ a b : ℝ, 0 ≤ a → b ≤ T →
       μ (Ico a b) = ν (Ico a b)) :
    μ.restrict (Ico 0 T) = ν.restrict (Ico 0 T) := by sorry
