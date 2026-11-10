-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_constant_weighted_count_variance
-- name    : AvramDividend.Classical.avram_mix_annulus16_original_constant_weighted_count_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:28:57.368198+00:00
-- url     : https://prove2.me/theorems/4f85fd76-a12a-4e6a-bc0d-62078917bf25
-- title:
--   Original negative-annulus compensated chronological count has exact deterministic-weight L2 energy
-- statement:
--   For the literal original Lévy path and its finite annulus of negative jumps, scaling the compensated physical count by any real coefficient preserves L2 integrability and scales the exact variance by the coefficient squared. This supplies quantitative mark-simple energy from original chronology for infinite small-jump isometry.
-- source:
--   Root connected 6ea0212e→6e234a3f (both Proved); quantitative original count weighted isometry needed by 5f12c023 positive-clock mixed infinite source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus16_original_constant_weighted_count_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) (c : ℝ) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (c * ((N ω).toReal - r)) ^ 2) P ∧
      (∫ ω, (c * ((N ω).toReal - r)) ^ 2 ∂P) = c ^ 2 * r := by sorry
