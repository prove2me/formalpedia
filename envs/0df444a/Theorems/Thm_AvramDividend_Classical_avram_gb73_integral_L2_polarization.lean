-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb73_integral_L2_polarization
-- name    : AvramDividend.Classical.avram_gb73_integral_L2_polarization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:12:59.721783+00:00
-- url     : https://prove2.me/theorems/b193f481-9edf-4289-a53e-604622a00e77
-- title:
--   Polarisation of integrable real squared differences
-- statement:
--   For real random variables with integrable squares and integrable product, the expected square of their difference equals the sum of their two expected squares minus twice the expected product. This elementary integral identity is used to make the physical two-grid Gaussian limit depend on diagonal and cross covariance convergence.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_gb73_integral_L2_polarization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ)
    (hf2 : Integrable (fun ω => (f ω) ^ 2) P)
    (hg2 : Integrable (fun ω => (g ω) ^ 2) P)
    (hprod : Integrable (fun ω => f ω * g ω) P) :
    (∫ ω, (f ω - g ω) ^ 2 ∂P) =
      (∫ ω, (f ω) ^ 2 ∂P) + (∫ ω, (g ω) ^ 2 ∂P) -
        2 * (∫ ω, f ω * g ω ∂P) := by sorry
