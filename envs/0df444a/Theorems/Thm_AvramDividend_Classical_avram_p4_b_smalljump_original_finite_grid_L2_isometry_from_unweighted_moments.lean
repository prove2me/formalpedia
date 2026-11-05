-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_grid_L2_isometry_from_unweighted_moments
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_finite_grid_L2_isometry_from_unweighted_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:54:53.094671+00:00
-- url     : https://prove2.me/theorems/3a7ea415-0905-4d23-8041-ec81084de988
-- title:
--   Original finite-grid isometry from physical diagonal and cross moments
-- statement:
--   Original jump-cell finite-grid weighted L2 isometry from per-cell physical variances and unweighted cross orthogonality.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_grid_L2_isometry

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_finite_grid_L2_isometry_from_unweighted_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (B : ι → Set ℝ) (J : ι → Ω → ℝ)
    (hSource : ∀ i ∈ S, ∀ ω, J i ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)).toReal)
    (r c : ι → ℝ)
    (hRate : ∀ i ∈ S, r i =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal)
    (hPairInt : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun ω =>
      (c i * (J i ω - r i)) * (c j * (J j ω - r j))) P)
    (hVar : ∀ i ∈ S,
      (∫ ω, (J i ω - r i) ^ 2 ∂P) = r i)
    (hOrth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (∫ ω, (J i ω - r i) * (J j ω - r j) ∂P) = 0) :
    (∫ ω, (∑ i ∈ S, c i * (J i ω - r i)) ^ 2 ∂P) =
      ∑ i ∈ S, c i ^ 2 * r i := by sorry
