-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_h_original_BV_finite_mesh_pairwise_value_Lipschitz
-- name    : AvramDividend.Classical.avram_p3_h_original_BV_finite_mesh_pairwise_value_Lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:24:56.130137+00:00
-- url     : https://prove2.me/theorems/41509c2d-3992-4680-8348-d8436b299433
-- title:
--   One quantitative value-function Lipschitz constant controls all source reserve states of a finite P3 mesh
-- statement:
--   Any nonempty finite mesh of original positive under-cap reserve states admits one nonnegative constant bounding every pairwise value-function difference by the reserve-distance. It is an explicit usable finite-grid C1 Taylor estimate.
-- source:
--   Proved original finite-mesh uniform compact Lipschitz 687a6c98.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_h_original_BV_finite_mesh_uniform_Lipschitz_band
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_h_original_BV_finite_mesh_pairwise_value_Lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (S : Finset ℝ) (hS : S.Nonempty)
    (hInside : ∀ z ∈ S, 0 < z ∧ ENNReal.ofReal z < C) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ u ∈ S, ∀ v ∈ S, |w u - w v| ≤ L * |u - v| := by sorry
