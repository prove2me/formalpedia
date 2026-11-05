-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_of_cell_L2
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_of_cell_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:21:11.668712+00:00
-- url     : https://prove2.me/theorems/87f99d6a-e7a7-4b70-8476-75b2643142e0
-- title:
--   Original intrinsic finite predictable-grid L2 isometry from individual cell L2
-- statement:
--   For the actual original intrinsic finite negative-band counts of X, the verified physical predictable grid L2 isometry holds given individual cell MemLp 2 instead of independently assuming integrability of every finite prefix squared sum. Conditional second moments and source integrability remain explicit; no synthetic Poisson process.
-- source:
--   Proved/public P4-G prefix L2 1574cca8 (candidate 26999) and proved/public original physical finite-grid isometry 8faf050d (candidate 26998).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_finite_prefix_square_integrable_of_cell_L2
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_predictable_grid_auto_meas

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_of_cell_L2
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
    (H D : ℕ → Ω → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hPairL2 : ∀ i, MemLp (fun ω =>
      (∑ j ∈ Finset.range i, D j ω) * H i ω) 2 P)
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal - r i) 2 P)
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕 (grid i)] =ᵐ[P] (fun _ => r i))
    (hSq : ∀ i, Integrable (fun ω =>
      ((N i ω).toReal - r i) ^ 2) P)
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hWSq : ∀ i, Integrable (fun ω =>
      (H i ω) ^ 2 * ((N i ω).toReal - r i) ^ 2) P)
    (hCellL2 : ∀ i, MemLp (D i) 2 P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
