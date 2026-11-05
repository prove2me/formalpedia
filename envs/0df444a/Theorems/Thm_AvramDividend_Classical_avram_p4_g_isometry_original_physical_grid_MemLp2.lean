-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_physical_grid_MemLp2
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_physical_grid_MemLp2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:04:13.70329+00:00
-- url     : https://prove2.me/theorems/f107220d-0238-4173-b49d-e39b0f32aa72
-- title:
--   Physical original intrinsic finite-grid predictable compensated sum belongs to L2(P)
-- statement:
--   For original X and actual NX finite negative mark bands, physical chronological pair expected intensity gives centred count L2. Bounded adapted coefficients yield L2 increments using the pinned L2-times-Linfty diagonal integrability result; the finite original physical compensated sum is genuinely in L2(P). This result makes actual square integrability explicit alongside the accepted isometry equality, avoiding any totalised-integral ambiguity.
-- source:
--   Proved source physical centred count L2 e0edd902, accepted L2/Linfty diagonal integrability and finite prefix MemLp theorem. Pair mean physical premise explicit, future sigma independence not needed for membership.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_physical_band_centred_count_L2
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_integrable_diagonals_of_L2_Linfty
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_finite_prefix_memLp_of_cells

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_physical_grid_MemLp2
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
    (n : ℕ) :
    MemLp (fun ω => ∑ i ∈ Finset.range n, D i ω) 2 P := by sorry
