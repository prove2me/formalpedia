-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_native_positive_root_derivative_coefficient
-- name    : AvramDividend.Classical.avram_ws01e_cr_new_native_positive_root_derivative_coefficient
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:29:55.804337+00:00
-- url     : https://prove2.me/theorems/0dbaa368-3668-48f6-82a3-c95031e2ef9f
-- title:
--   The native positive-root Lévy–Khintchine drift coefficient equals the actual Esscher derivative
-- statement:
--   For any canonical spectrally negative Lévy process with a positive root φ and a genuine full derivative m=ψ′(φ), identify m with the exact linear coefficient of the remotely Proved source-specific Esscher Volterra denominator. The correction for a jump of magnitude exactly one is retained. Use the integrable nonnegative double-tail kernel to show the quadratic remainder divided by the positive shift vanishes. This makes the killing coefficient in the positive ladder-height Bernstein representation genuinely positive when combined with the already Proved root derivative positivity.
-- source:
--   The pinned canonical laplaceExponent formula; remotely Proved gaussian_native_esscher_real_kernel_denominator (93b9ef31) and gaussian_native_double_tail_kernel_full_regularity (aa1771a9); pinned HasDerivAt.tendsto_slope_zero_right. This is a source-specific coefficient identification, distinct from the accepted generic derivative-existence result.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_native_esscher_real_kernel_denominator
import Theorems.Thm_AvramDividend_Classical_gaussian_native_double_tail_kernel_full_regularity

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_cr_new_native_positive_root_derivative_coefficient
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ m : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hm : HasDerivAt X.ψ m φ) :
    m =
      X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
        ∂(X.ν.map (fun y : ℝ => -y))) := by sorry
