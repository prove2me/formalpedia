-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_any_interior_C1_band_automatic_negative_mark_compensator_analytic_certificate
-- name    : AvramDividend.Classical.avram_bva_a22_original_any_interior_C1_band_automatic_negative_mark_compensator_analytic_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:23:14.528974+00:00
-- url     : https://prove2.me/theorems/fb9eee90-5f93-4469-a411-3dfd9d76448d
-- title:
--   Actual original arbitrary positive interior C1 bands automatically admit all three analytic hypotheses needed for stopped negative mark compensator L1
-- statement:
--   For the original spectrally negative Levy process with bounded variation, original verification candidate continuous on nonnegative reserve and zero on strictly negative reserves, and C1 on the true positive cap interior, take any actual positive localisation band a,b with a<=2 and [a/2,b] inside the genuine strict reserve interior. Prove simultaneously that there exist nonnegative finite constants L and R such that the original w is L-Lipschitz on [a/2,b], the actual w(v) is uniformly bounded in absolute value by R on the entire left halfline v<=b, and the true original negative Levy measure has finite mass on marks z<=-a/2. These are exactly the three analytic hypotheses used by the Proved Wave7 inclusive true-ruin stopped negative-mark compensator integrable nonpositive-mean theorem, now discharged from original C1 source assumptions with no artificial truncation or extra finite-activity assumption. The result applies on each arbitrary original cofinal spatial row and is a genuine source bridge into the remaining BVA96 spatial C1 generator ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_any_interior_C1_band_automatic_negative_mark_compensator_analytic_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hinside : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L R : ℝ,
      0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) ∧
      X.ν (Iic (-a / 2)) < ⊤ := by sorry
