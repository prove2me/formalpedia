-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_renewal_positive_convolution_powers_no_atom
-- name    : AvramDividend.Classical.geometric_renewal_positive_convolution_powers_no_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:29:31.311995+00:00
-- url     : https://prove2.me/theorems/4df9ee38-6a77-4311-a441-f1a71af23ab1
-- title:
--   Positive convolution powers of a Lebesgue-continuous renewal kernel have no origin atom
-- statement:
--   Let the first renewal kernel be absolutely continuous with respect to Lebesgue measure. Every strictly positive-order convolution power generated from it is also absolutely continuous, and in particular has zero mass at the origin. This is the exact higher-order atomlessness condition for identifying the bounded-variation scale origin from the canonical geometric renewal measure.
-- source:
--   Mathlib Measure.conv_absolutelyContinuous, applied using the Proved renewal_measure_ac_on_positive (563ee480-72e9-405a-ac26-09db3ed399b7); canonical Esscher scale representation (bd5082fb-392c-4e36-9858-95c79a31ed92).

import Theorems.Thm_AvramDividend_Classical_renewal_measure_ac_on_positive
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.geometric_renewal_positive_convolution_powers_no_atom
    (κ : Measure ℝ) [SFinite κ] (m : ℕ → Measure ℝ)
    (hmsf : ∀ n : ℕ, SFinite (m n))
    (hκ : κ ≪ (volume : Measure ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) = κ.conv (m n)) :
    ∀ n : ℕ, 0 < n → m n ({(0 : ℝ)} : Set ℝ) = 0 := by sorry
