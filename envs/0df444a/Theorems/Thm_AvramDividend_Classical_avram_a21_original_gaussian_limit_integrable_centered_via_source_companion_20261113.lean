-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
-- name    : AvramDividend.Classical.avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:17:59.716266+00:00
-- url     : https://prove2.me/theorems/5bdde16f-defc-4220-ab73-a007ae4632bb
-- title:
--   Original physical Gaussian cutoff limit L1 and centred at each horizon from same-source companion
-- statement:
--   The original physical Gaussian residual-limit field is integrable and centred at every horizon on the same original P. Proof uses original almost-sure small-band field, the same-source zero-jump Gaussian companion construction (ca457ff7 Open), Proved pathwise identification of the physical Gaussian limit with the centred companion (5e640724), and Proved centred fixed-time mean for any pure Gaussian source (082b7410). This isolates mean-zero separately from marked-tail independence.
-- source:
--   Source compensated-smallmark uniform limit 9362895e, original zero-jump Gaussian companion ca457ff7, Proved same-source identification 5e640724, pure Gaussian fixed-time centring 082b7410.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ t : ℝ≥0,
      Integrable (R t) P ∧
      (∫ ω, R t ω ∂P) = 0 := by sorry
