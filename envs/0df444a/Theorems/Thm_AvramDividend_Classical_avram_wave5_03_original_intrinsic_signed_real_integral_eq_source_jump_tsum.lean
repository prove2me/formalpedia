-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum
-- name    : AvramDividend.Classical.avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:35:49.194014+00:00
-- url     : https://prove2.me/theorems/c1360947-7197-4b2d-8178-1535c19e5748
-- title:
--   Signed real Itô jump integrand equals source-path Lévy intrinsic marked measure integral under true integrability
-- statement:
--   For the original spectrally negative Levy path, the genuine intrinsic marked jump measure on the same Ω, defined by positive-time nonzero actual source jumps, integrates any measurable integrable real signed mark kernel f to the actual unrestricted sum of its values over the original jumps. Unlike the already Proved nonnegative ENNReal source integral e4542c93, this is a signed Bochner integral, required to represent controlled Ito–Meyer generator Taylor kernels without artificially taking positive parts. Preserve explicit integrability and do not assume a Poisson/compensator law or independent source.
-- source:
--   Original Levy jump graph via Proved avram_wave4_04a_actual_levy_jumpmark_joint_measurable; same source counting measure as Proved e4542c93, now signed real and integrable; direct Chat03 controlled Ito–Meyer bridge to BV ef7e6c20 and UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (f : (ℝ≥0 × ℝ) → ℝ) (hf : Measurable f)
    (hfin : Integrable f
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) :
    (∫ p, f p ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑' u : ℝ≥0, if 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
      then f (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      else 0 := by sorry
