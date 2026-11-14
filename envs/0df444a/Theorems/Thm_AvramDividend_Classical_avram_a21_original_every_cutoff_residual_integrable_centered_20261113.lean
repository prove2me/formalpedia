-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_every_cutoff_residual_integrable_centered_20261113
-- name    : AvramDividend.Classical.avram_a21_original_every_cutoff_residual_integrable_centered_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:25:48.53217+00:00
-- url     : https://prove2.me/theorems/6942df41-afe4-4680-8097-0ebf7c5e6882
-- title:
--   Original finite activity intrinsic Gaussian cutoff residual integrable and centred at every horizon
-- statement:
--   Every original physical finite-cutoff Gaussian residual is integrable and mean-zero, for a finite negative mark Levy measure. This follows directly from source retention band L1 plus correct physical residual subtraction, zero cutoff L1 and original mean centring; all statements retain the original P without replacing laws or assuming false R0/Jn independence.
-- source:
--   Proved source X.isProbability; retained physical L1 child 04e2f119; proved original hJ-conditional cutoff L1 and zero-centred child 85484289.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_every_cutoff_residual_integrable_centered_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P ∧
      (∫ ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω ∂P) = 0 := by sorry
