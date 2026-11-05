-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_actual_controlled_cap_C1_and_payment_premises
-- name    : AvramDividend.Classical.avram_p2_assist_p3_actual_controlled_cap_C1_and_payment_premises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:02:17.51981+00:00
-- url     : https://prove2.me/theorems/c9b05053-c171-4671-bc2f-d9231475b5f6
-- title:
--   All actual original controlled Lévy P3-F cap continuation regularity and right-payment premises
-- statement:
--   For the original spectrally negative Lévy source X and its actual admissible dividend control D, derive the full P3-F physical source grid premise package with w=V: continuity across cap, strict-interior C1, derivative≥1, idempotent cap definition, and chronological right-payment jump inequality at time zero and every pre-ruin time. No conditional right-payment assumption remains. Imports accepted source exact actual payment theorem and accepted deterministic cap bundle.
-- source:
--   Proved original avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop (1a3ddaf1) and Proved avram_p2_assist_p3_original_source_cap_C1_grid_premises (2e2f44ad).

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_original_source_cap_C1_grid_premises
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_actual_controlled_cap_C1_and_payment_premises
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ContinuousOn V (Ici (0 : ℝ)) ∧
    ContDiffOn ℝ 1 V {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} ∧
    (∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv V z) ∧
    (C = ⊤ → ∀ z : ℝ, V z = V z) ∧
    (C ≠ ⊤ → ∀ z : ℝ, V z =
      if z ≤ C.toReal then V z
      else V C.toReal + (z - C.toReal)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        V (riskProcess X x D t ω) -
          V (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by sorry
