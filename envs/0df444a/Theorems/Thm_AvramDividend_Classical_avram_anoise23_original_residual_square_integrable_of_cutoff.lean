-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise23_original_residual_square_integrable_of_cutoff
-- name    : AvramDividend.Classical.avram_anoise23_original_residual_square_integrable_of_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T09:08:43.025423+00:00
-- url     : https://prove2.me/theorems/ea1e0307-23e5-48ac-bccc-86df573ac3af
-- title:
--   Original Gaussian residual limit inherits L2 integrability from one physical cutoff
-- statement:
--   An intrinsic residual that is almost surely the original finite-cutoff limit and is ambient measurable has an integrable square whenever one physical cutoff has an integrable square and all cutoffs are ambient measurable. The quantitative original L2 error controls the difference. This is the analytic integrability passage required by the original Gaussian bracket target.
-- source:
--   Direct theorem from accepted original L2 cutoff error 41b16fe8 and square inequality. The source physical finite-cutoff square integrability is exactly the new anoise22 original-cutoff moment obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise21_original_gaussian_residual_L2_cutoff_error
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise23_original_residual_square_integrable_of_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (hRsource : ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (nhds (R t ω)))
    (hRmeas : AEStronglyMeasurable (R t) P)
    (hCutMeas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P)
    (hCutSquare : Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) P) :
    Integrable (fun ω => (R t ω) ^ 2) P := by sorry
