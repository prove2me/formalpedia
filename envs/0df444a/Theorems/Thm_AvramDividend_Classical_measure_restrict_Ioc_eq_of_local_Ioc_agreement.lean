-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_restrict_Ioc_eq_of_local_Ioc_agreement
-- name    : AvramDividend.Classical.measure_restrict_Ioc_eq_of_local_Ioc_agreement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:41:40.230003+00:00
-- url     : https://prove2.me/theorems/7ba7a474-1bb0-41c0-accf-4988e71a3c3f
-- title:
--   Finite-window measure equality from agreement on all interior half-open intervals
-- statement:
--   Two Borel measures on the real line which agree on every half-open subinterval contained in the closed time window [0,T] define equal restricted measures on (0,T], provided the first measure has finite total mass there. This is the exact uniqueness step for upgrading the linear pre-first-jump Stieltjes interval masses to discounted integrals against Lebesgue measure.
-- source:
--   Borel measure uniqueness on the generating family of half-open intervals; applied to Avram, Palmowski and Pistorius (2007), Section 3.3.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.measure_restrict_Ioc_eq_of_local_Ioc_agreement
    (μ ν : Measure ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hFinite : μ (Ioc 0 T) < ⊤)
    (hEq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      μ (Ioc s t) = ν (Ioc s t)) :
    μ.restrict (Ioc 0 T) = ν.restrict (Ioc 0 T) := by sorry
