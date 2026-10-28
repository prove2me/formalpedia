-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_le_of_strict_terminal_positive_truncations
-- name    : AvramDividend.Classical.lintegral_le_of_strict_terminal_positive_truncations
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:54:12.739384+00:00
-- url     : https://prove2.me/theorems/9adaa9d6-6437-4716-b8b0-da12a0025cf1
-- title:
--   Strictly preterminal positive-time bounds imply the full stopped integral bound
-- statement:
--   For a measurable stopped-payment region lying strictly before a finite positive terminal time T, if its restricted measure has no nonpositive-time mass and its discounted integrals through every finite cutoff t<T are bounded above by B, then its complete nonnegative integral is bounded by B. Rational cutoffs strictly between each payment time and T form a countable directed exhaustion, and monotone convergence supplies the full limit.
-- source:
--   Use rational density (exists_rat_btwn), directed monotone convergence for ℚ-subtype cutoffs, the restricted-measure support lemma and each preterminal truncated integral bound.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.lintegral_le_of_strict_terminal_positive_truncations
    (μ : Measure ℝ) (T : ℝ) (hT : 0 < T)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hST : ∀ r ∈ S, r < T)
    (hzero : (μ.restrict S) (Set.Iic (0 : ℝ)) = 0)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (B : ℝ≥0∞)
    (hbound : ∀ t : ℝ, 0 ≤ t → t < T →
      (∫⁻ r in S, if r ∈ Set.Ioc (0 : ℝ) t then f r else 0 ∂μ) ≤ B) :
    (∫⁻ r in S, f r ∂μ) ≤ B := by sorry
