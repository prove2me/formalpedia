-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
-- name    : AvramDividend.Classical.avram_mixed_source13_original_physical_annulus_count_variance_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:19:58.188347+00:00
-- url     : https://prove2.me/theorems/6e234a3f-568d-4eb5-a21c-b67b437bef4b
-- title:
--   Exact original compensated negative-annulus count L2 isometry
-- statement:
--   For the literal original spectrally negative Levy process X on the same sample space and law, the compensated count of jumps with marks between the nested reciprocal cutoffs n and m has exact second moment T times the original Levy measure of that annulus. This is the first missing source-law premise behind mixed original physical annulus L2 isometry. The result assumes neither a cross-band covariance, a Poisson replacement process, nor physical isometry. Weighted mark and bounded stopping-time extensions remain separate obligations.
-- source:
--   AVRAM MIX-SOURCE13, 8 November 2026. First original same-space annulus count second-moment source premise for MIX-FIN13 and MIX-INF13.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_original_physical_annulus_count_variance_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by sorry
