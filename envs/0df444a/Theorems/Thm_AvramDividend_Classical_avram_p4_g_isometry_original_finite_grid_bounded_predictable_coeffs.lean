-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_bounded_predictable_coeffs
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_bounded_predictable_coeffs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:40:42.793826+00:00
-- url     : https://prove2.me/theorems/a182a776-1d1f-4607-ae6a-2658c1838b68
-- title:
--   Original intrinsic finite-grid L2 isometry for bounded predictable coefficients
-- statement:
--   For intrinsic finite negative-mark-band counts of the original spectrally negative Levy process, an essentially bounded predictable coefficient and L2 centred count give cell and prefix cross-term L2 automatically; the physical finite predictable-grid isometry follows from the source conditional second-moment and remaining explicit integrability hypotheses.
-- source:
--   Conditional original rectangle variance; original physical finite-grid isometry and MemLp L2/Linfty product lemmas; no synthetic Poisson count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_L2_product_of_predictable_Linfty
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_finite_prefix_memLp_of_cells
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_of_cell_L2

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_bounded_predictable_coeffs
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
    (hHInf : ∀ i, MemLp (H i) ⊤ P)
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal - r i) 2 P)
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕 (grid i)] =ᵐ[P] (fun _ => r i))
    (hSq : ∀ i, Integrable (fun ω =>
      ((N i ω).toReal - r i) ^ 2) P)
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hWSq : ∀ i, Integrable (fun ω =>
      (H i ω) ^ 2 * ((N i ω).toReal - r i) ^ 2) P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
