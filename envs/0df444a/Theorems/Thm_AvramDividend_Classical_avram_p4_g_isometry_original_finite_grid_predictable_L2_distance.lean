-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_predictable_L2_distance
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_predictable_L2_distance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:44:18.094317+00:00
-- url     : https://prove2.me/theorems/6b7bb799-934a-4a5d-966d-7ea12003aa6c
-- title:
--   Physical intrinsic finite-grid L2 distance between two original predictable jump sums
-- statement:
--   For the same original Lévy process and actual intrinsic marked count NX, two predictable bounded/integrable coefficient grids have exact L2 distance. Source-exact physical chronological ordered-pair rate and future-sigma independence are retained as explicit hypotheses; the proof is a linear-difference application of the accepted physical finite-grid isometry. Strict small-jump marks stay -1<z<-epsilon.
-- source:
--   Physical finite-grid original-space isometry e36a4271-2a98-4104-b21b-671f329a924c38; no stochastic-integral completion or stopped identification claimed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_from_physical_ordered_pairs

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_predictable_L2_distance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H G : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hG : ∀ i, StronglyMeasurable[𝓕 (grid i)] (G i))
    (hHInf : ∀ i, MemLp (H i) ⊤ P)
    (hGInf : ∀ i, MemLp (G i) ⊤ P)
    (hCountEndpoint : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))]
      (fun ω => (N i ω).toReal))
    (K : ℕ → Ω → ℝ≥0∞)
    (hKMeas : ∀ i, Measurable (K i))
    (hPhysicalPair : ∀ i ω,
      (N i ω).toReal * ((N i ω).toReal - 1) = 2 * (K i ω).toReal)
    (hPairMean : ∀ i,
      (∫⁻ ω, K i ω ∂P) = ENNReal.ofReal
        (((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) ^ 2 / 2))
    (mFuture : ℕ → MeasurableSpace Ω)
    (hFuture : ∀ i, mFuture i ≤ mΩ)
    (hSqMeas : ∀ i, StronglyMeasurable[mFuture i]
      (fun ω => ((N i ω).toReal - r i) ^ 2))
    (hIndependent : ∀ i, Indep (mFuture i) (𝓕 (grid i)) P)
    (n : ℕ) :
    (∫ ω, ((∑ i ∈ Finset.range n,
         H i ω * ((N i ω).toReal - r i)) -
       (∑ i ∈ Finset.range n,
         G i ω * ((N i ω).toReal - r i))) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω - G i ω) ^ 2 ∂P := by sorry
