-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_rightcont_physical_grid_isometry_adapted_auto
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_original_rightcont_physical_grid_isometry_adapted_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:07:41.372023+00:00
-- url     : https://prove2.me/theorems/789130fc-4e2e-4985-b03a-27e60931fcd1
-- title:
--   Exact original right-continuous physical grid L2 isometry with adapted prefixes automatically derived
-- statement:
--   True original separated marked-jump cells with a bounded past-measurable predictable coefficient, an actual terminal-count measurability certificate and a genuine conditional-square moment have exact finite-grid L2 energy. The formerly separate hPrefix is derived automatically from the completed-cell measurability and monotone filtration, matching original UBV stopping grids.
-- source:
--   Imports Proved original right-continuous physical grid isometry 66ac8bb6 and newly authored run1640 terminal cell and predictable prefix closure. No extra stochastic assumption other than source hNEnd and honest conditional variance.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_original_rightcont_physical_grid_isometry_adapted_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hFinite : ∀ i, X.ν (B i) < ⊤)
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
    (H D : ℕ → Ω → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (hNEnd : ∀ i, StronglyMeasurable[𝓕.rightCont (grid (i + 1))]
      (fun ω => (N i ω).toReal))
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕.rightCont (grid i)] =ᵐ[P] (fun _ => r i))
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
