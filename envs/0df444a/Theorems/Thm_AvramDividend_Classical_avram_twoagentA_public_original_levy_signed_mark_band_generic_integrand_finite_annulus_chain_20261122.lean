-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_levy_signed_mark_band_generic_integrand_finite_annulus_chain_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_levy_signed_mark_band_generic_integrand_finite_annulus_chain_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:05:28.120639+00:00
-- url     : https://prove2.me/theorems/e28ee4ed-5336-473c-a609-695066655574
-- title:
--   Original signed-mark quantizer proof reusable original_levy_signed_mark_band_generic_integrand_finite_annulus_chain_20261122
-- statement:
--   Republish the verbatim remotely accepted private proof as an independently importable PUBLIC original-physical negative-mark finite-band signed integral bridge helper, with the mathematical statement unchanged. The source has no private theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_levy_signed_mark_band_generic_integrand_finite_annulus_chain_20261122
    (ν : Measure ℝ) (a : ℕ → ℝ) (ha : Monotone a)
    (f : ℝ → ℝ) (n m : ℕ) (hnm : n ≤ m)
    (hInt : IntegrableOn f (Ioc (a n) (a m)) ν) :
    (∫ z in Ioc (a n) (a m), f z ∂ν) =
      ∑ i ∈ Finset.Ico n m,
        (∫ z in Ioc (a i) (a (i + 1)), f z ∂ν) := by sorry
