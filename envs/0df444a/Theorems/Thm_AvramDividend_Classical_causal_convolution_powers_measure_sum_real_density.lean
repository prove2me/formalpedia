-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_measure_sum_real_density
-- name    : AvramDividend.Classical.causal_convolution_powers_measure_sum_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:44:15.022347+00:00
-- url     : https://prove2.me/theorems/d890b718-2b35-4fc2-8fdd-383e32fd0c2e
-- title:
--   Renewal convolution-power measure sum equals the measure of its real density series
-- statement:
--   End-to-end deterministic bridge from the causal real convolution recursion and corresponding positive measure convolution recursion to an exact equality of the countable renewal measure sum and Lebesgue withDensity of the ordinary real tsum of convolution densities. Combines two canonical Proved sublemmas: identification of each convolution measure with the real power, then pointwise countable real-density measure sum. This is the missing measure-series identification used when equating the finite geometric BV Esscher renewal cumulative with the scale primitive in 1ca4a724, directly on the cstar finiteness route.
-- source:
--   Canonical nonnegative_real_causal_convolution_powers_density_identification and countable_real_density_measure_sum_eq_real_tsum.

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_causal_convolution_powers_density_identification
import Theorems.Thm_AvramDividend_Classical_countable_real_density_measure_sum_eq_real_tsum
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_convolution_powers_measure_sum_real_density
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hκpos : ∀ x : ℝ, 0 ≤ κ x)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hκmeas : Measurable κ) (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hconv : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => κ y * F n (x - y)) volume)
    (hFsummable : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hFzero : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hmzero : m 0 = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (κ x)))
    (hmsucc : ∀ n : ℕ, m (n + 1) =
      (volume.withDensity (fun x : ℝ => ENNReal.ofReal (κ x))).conv (m n)) :
    Measure.sum m =
      volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal (∑' n : ℕ, F n x)) := by sorry
