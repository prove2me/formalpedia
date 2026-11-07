-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_C1_compact_Lipschitz_deriv_certificate
-- name    : AvramDividend.Classical.avram_bv_error7_original_C1_compact_Lipschitz_deriv_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:46:40.791236+00:00
-- url     : https://prove2.me/theorems/eecd0a2e-94ac-4e1a-8b44-2476caec3569
-- title:
--   Actual original positive-subcap C1 dividend value has one finite compact-band Lipschitz and derivative envelope
-- statement:
--   Under the exact original dividend C1 and open positive-subcap assumptions, every compact interior interval Icc a b contained in that domain admits one nonnegative real L that simultaneously bounds the derivative magnitude everywhere and makes w L-Lipschitz on every pair of interval points. This completely discharges the analytic global Taylor-envelope hypotheses from the original C1 statement with no artificial regularity extension to ruin/cap boundaries.
-- source:
--   Composition of original C1 band differentiability/derivative continuity child avram_bv_error7_original_C1_band_deriv_continuous_differentiable (authoring job 37daca29-a169-44d9-8f4c-140928911685) and compact real mean-value certificate avram_bv_error7_compact_derivative_uniform_lipschitz_certificate (authoring job 24769e96-583b-4237-977d-010ac8973293). Intended direct source adapter to original BV positive error mean theorem 681ee517.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_C1_compact_Lipschitz_deriv_certificate
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
        |w z - w y| ≤ L * |z - y|) ∧
      (∀ y ∈ Set.Icc a b, |deriv w y| ≤ L) := by sorry
