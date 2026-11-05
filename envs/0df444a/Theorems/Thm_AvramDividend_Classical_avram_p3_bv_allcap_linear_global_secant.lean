-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_global_secant
-- name    : AvramDividend.Classical.avram_p3_bv_allcap_linear_global_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:18:48.525197+00:00
-- url     : https://prove2.me/theorems/5907ddca-d6f1-4ea3-9879-e7f3a6b91707
-- title:
--   BV cap-linear HJB continuation has global dividend secants at finite or infinite cap
-- statement:
--   For every strictly positive cap, finite or infinite, and canonical original BV HJB candidate continuous at nonnegative reserves, continuously differentiable on the strict interior, with derivative at least one there, the cap-linear extension V has global dividend secants b-a ≤ V(b)-V(a) for all 0≤a≤b. At infinite cap V=w; at finite cap V agrees with w below the cap and has exact slope one above. No above-cap differentiability or extra smooth-fit assumption is needed. This combines the original BV cap-contact cases into one importable theorem for the stopped verification mesh.
-- source:
--   Finite cap: proved crossing plus global finite-cap extension secant 849da3fc-079a-43c1-86c9-f1144c420b48; infinite cap: directly proved BV full-cap gradient secant 2ba5cc4f-3aab-40ea-a59a-8a49633c7595. No stochastic limit inferred from this deterministic lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_global_secant

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_allcap_linear_global_secant
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b - a ≤ V b - V a := by sorry
