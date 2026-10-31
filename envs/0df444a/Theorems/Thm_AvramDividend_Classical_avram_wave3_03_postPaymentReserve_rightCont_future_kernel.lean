-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_postPaymentReserve_rightCont_future_kernel
-- name    : AvramDividend.Classical.avram_wave3_03_postPaymentReserve_rightCont_future_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:06:22.128212+00:00
-- url     : https://prove2.me/theorems/28b89d1b-7794-4017-9495-7fc146a6d115
-- title:
--   Original post-payment controlled reserve has the exact right-continuous past and Levy future-path kernel
-- statement:
--   For the original spectrally negative Levy process and any actual adapted dividend strategy, at every deterministic time s the controlled reserve after the right-limit dividend payment and the entire future Levy increment path factorise under every measurable nonnegative joint test, even when restricted to an event measurable in the right-continuous past filtration. This is the source-specific conditioning interface for a post-payment stochastic dividend grid step.
-- source:
--   The identical Levy process transported to the right-continuous filtration, the previously Proved adaptedness of the actual post-payment reserve, and the previously Proved deterministic-time source future-path product-kernel theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave3_03_postPaymentReserve_rightCont_future_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont s] A)
    (f : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, (if ω ∈ A then
        f (x + X.X s ω - rightLimit D s ω,
          fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
      else (0 : ℝ≥0∞)) ∂P) =
    (∫⁻ ω, (if ω ∈ A then
        ∫⁻ y, f (x + X.X s ω - rightLimit D s ω, y)
          ∂(Measure.map (fun ζ => (fun t : ℝ≥0 => X.X t ζ)) P)
      else (0 : ℝ≥0∞)) ∂P) := by sorry
