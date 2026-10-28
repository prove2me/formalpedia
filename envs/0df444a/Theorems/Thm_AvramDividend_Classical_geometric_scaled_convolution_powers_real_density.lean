-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_scaled_convolution_powers_real_density
-- name    : AvramDividend.Classical.geometric_scaled_convolution_powers_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:27:51.090763+00:00
-- url     : https://prove2.me/theorems/fe0ec21c-f478-46e0-825a-0a6d8a4e2ae0
-- title:
--   Every geometrically weighted convolution power has the corresponding real density
-- statement:
--   Let κ be an s-finite real measure, let c be a nonnegative extended-real multiplier, and suppose c•κ is the Lebesgue-density measure of a nonnegative measurable real function k. If m_n are the successive unweighted convolution powers of κ, and F_n are the matching nonnegative integrable real convolution powers of k, then c^(n+1)•m_n is precisely the measure with density F_n for every n. This uses the newly Proved two-scalar convolution scaling and the Proved causal convolution-power density identification. It is the substantive missing weighted-measure-to-real-density implication required by the geometric-renewal atom-plus-density result and the BV Esscher cstar finiteness route.
-- source:
--   Canonical Proved double_scalar_measure_convolution and nonnegative_real_causal_convolution_powers_density_identification.

import Mathlib.MeasureTheory.Group.Convolution
import Theorems.Thm_AvramDividend_Classical_double_scalar_measure_convolution
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_causal_convolution_powers_density_identification
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.geometric_scaled_convolution_powers_real_density
    (c : ℝ≥0∞) (κ : Measure ℝ) [SFinite κ]
    (k : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hkpos : ∀ x : ℝ, 0 ≤ k x)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hkmeas : Measurable k) (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hconv : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => k y * F n (x - y)) volume)
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume)
    (hκscaled : c • κ = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (k x)))
    (hmzero : m 0 = κ)
    (hmsucc : ∀ n : ℕ, m (n + 1) = κ.conv (m n))
    (hmsfinite : ∀ n : ℕ, SFinite (m n)) :
    ∀ n : ℕ, c ^ (n + 1) • m n =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x)) := by sorry
