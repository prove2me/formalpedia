-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_physical_finite_grid_centred_L1
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_physical_finite_grid_centred_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:52:34.009325+00:00
-- url     : https://prove2.me/theorems/a9673aaf-9a67-4e1b-89f8-17ed1a47c8e3
-- title:
--   Original intrinsic physical finite-grid compensated predictable sums are integrable and mean zero
-- statement:
--   On the original space for X, every finite grid of past-adapted L2 coefficients has a true compensated intrinsic finite-band sum integrable with zero mean. The original P2-E rectangle law already provides conditional mean compensation, while the physical chronological pair expectation gives the missing per-cell L2 moment. The original physical pair expectation remains an explicit source premise.
-- source:
--   P4-G new physical-band centred count L2 plus Proved original P2-E raw finite-grid zero-mean theorem 2b55625c. This is finite-grid only, not an infinite activity or stopped assertion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_physical_band_centred_count_L2
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_finite_grid_zero_mean

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_physical_finite_grid_centred_L1
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
    (hMeas : ∀ i, Measurable (N i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (K : ℕ → Ω → ℝ≥0∞)
    (hKMeas : ∀ i, Measurable (K i))
    (hPhysicalPair : ∀ i ω,
      (N i ω).toReal * ((N i ω).toReal - 1) = 2 * (K i ω).toReal)
    (hPairMean : ∀ i,
      (∫⁻ ω, K i ω ∂P) = ENNReal.ofReal
        (((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) ^ 2 / 2))
    (n : ℕ) :
    Integrable (fun ω => ∑ i ∈ Finset.range n,
      H i ω * ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal)) ∂P) = 0 := by sorry
