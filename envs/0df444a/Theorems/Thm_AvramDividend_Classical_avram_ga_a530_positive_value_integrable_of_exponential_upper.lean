-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a530_positive_value_integrable_of_exponential_upper
-- name    : AvramDividend.Classical.avram_ga_a530_positive_value_integrable_of_exponential_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:27:32.078206+00:00
-- url     : https://prove2.me/theorems/1544c89b-4ae1-452a-9f42-452b252bebd4
-- title:
--   Positive part of a value with a one-sided exponential upper envelope is integrable
-- statement:
--   If a nonnegative random endpoint has an integrable exponential moment, a real value function bounded above by a nonnegative multiple of that exponential on the positive half-line (including the origin) has integrable positive part at the endpoint. This is a one-sided moment estimate for original Gaussian spatial source cells.
-- source:
--   One-sided exponential upper bound of HJB super-solutions (Proved a257), Gaussian stopped source exponential integrability (Proved gledger69), and Mathlib Integrable.mono for nonnegative positive parts.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a530_positive_value_integrable_of_exponential_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (Z : Ω → ℝ) (θ K : ℝ)
    (hK : 0 ≤ K) (h0 : w 0 ≤ K)
    (hupper : ∀ y : ℝ, 0 < y → w y ≤ K * Real.exp (θ * y))
    (hZ : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hExp : Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMeas : AEStronglyMeasurable
      (fun ω => max (w (Z ω)) (0 : ℝ)) P) :
    Integrable (fun ω => max (w (Z ω)) (0 : ℝ)) P := by sorry
