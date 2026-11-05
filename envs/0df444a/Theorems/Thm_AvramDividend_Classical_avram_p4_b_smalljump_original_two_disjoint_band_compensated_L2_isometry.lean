-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_two_disjoint_band_compensated_L2_isometry
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_two_disjoint_band_compensated_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:20:22.969361+00:00
-- url     : https://prove2.me/theorems/441c6399-df46-4175-9f16-7fde3c1c817e
-- title:
--   Original two disjoint finite-band compensated L2 isometry
-- statement:
--   Two original Lévy intrinsic marked-count cells with correct diagonal second moments and zero compensated covariance have the exact quadratic budget for a linear combination.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_two_disjoint_band_compensated_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (A B : Set ℝ) (hDisjoint : Disjoint A B)
    (JA JB : Ω → ℝ)
    (hSourceA : ∀ ω, JA ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ A)).toReal)
    (hSourceB : ∀ ω, JB ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (rA rB : ℝ)
    (hRateA : rA = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν A)).toReal)
    (hRateB : rB = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hIA : Integrable (fun ω => (JA ω - rA) ^ 2) P)
    (hIB : Integrable (fun ω => (JB ω - rB) ^ 2) P)
    (hICross : Integrable (fun ω =>
      (JA ω - rA) * (JB ω - rB)) P)
    (hVarA : (∫ ω, (JA ω - rA) ^ 2 ∂P) = rA)
    (hVarB : (∫ ω, (JB ω - rB) ^ 2 ∂P) = rB)
    (hOrth : (∫ ω,
      (JA ω - rA) * (JB ω - rB) ∂P) = 0)
    (cA cB : ℝ) :
    (∫ ω, (cA * (JA ω - rA) + cB * (JB ω - rB)) ^ 2 ∂P) =
      cA ^ 2 * rA + cB ^ 2 * rB := by sorry
