-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_real_causal_convolution_powers_density_identification
-- name    : AvramDividend.Classical.nonnegative_real_causal_convolution_powers_density_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:23:37.353988+00:00
-- url     : https://prove2.me/theorems/70ab4d06-8c92-4fbb-b407-3c4a26fcbead
-- title:
--   Identify all causal measure convolution powers with their nonnegative real density recursion
-- statement:
--   Given a nonnegative measurable real renewal kernel κ and a sequence F of measurable nonnegative real convolution powers, together with pointwise integrability and the matching recursion for a sequence of finite convolution measures, prove by induction that each measure is exactly the Lebesgue withDensity measure of F n. The sole substantive step imports the separately published real_nonnegative_density_measure_convolution_eq_withDensity lemma. This directly bridges the positive geometric renewal measure in the Proved BV Esscher Laplace package and the continuous real renewal-power series needed by the Open scaled scale identification 1ca4a724.
-- source:
--   Canonical real_nonnegative_density_measure_convolution_eq_withDensity and simple Nat induction; pinned Mathlib Measure.conv.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_convolution_lconvolution_ofReal_bridge
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.nonnegative_real_causal_convolution_powers_density_identification
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hκpos : ∀ x : ℝ, 0 ≤ κ x)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hκmeas : Measurable κ) (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hconv : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => κ y * F n (x - y)) volume)
    (hFzero : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hmzero : m 0 = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (κ x)))
    (hmsucc : ∀ n : ℕ, m (n + 1) =
      (volume.withDensity (fun x : ℝ => ENNReal.ofReal (κ x))).conv (m n)) :
    ∀ n : ℕ, m n = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (F n x)) := by sorry
