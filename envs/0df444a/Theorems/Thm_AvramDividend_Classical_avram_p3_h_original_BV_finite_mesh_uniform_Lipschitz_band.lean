-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_h_original_BV_finite_mesh_uniform_Lipschitz_band
-- name    : AvramDividend.Classical.avram_p3_h_original_BV_finite_mesh_uniform_Lipschitz_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:16:19.809831+00:00
-- url     : https://prove2.me/theorems/687a6c98-7e8f-41dd-a651-800aba45f987
-- title:
--   Actual original BV finite interior reserve mesh admits one uniform stopped-source C1 Lipschitz envelope
-- statement:
--   Every nonempty finite collection of positive under-cap original BV reserve values admits one common compact band with a single pair of source-exact Lipschitz and value bounds. Supplies a reusable mesh-uniform prepayment stopped jump compensation hypothesis.
-- source:
--   New P3-H finite-mesh compact band, Proved original P3-G bounds 0990d837, Proved cap openness b917eaf2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_h_localise_finite_interior_mesh_reserves_common_band
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_h_original_BV_finite_mesh_uniform_Lipschitz_band
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
    ∃ a b L R : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧
      (∀ z ∈ S, z ∈ Icc a b) ∧
      0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by sorry
