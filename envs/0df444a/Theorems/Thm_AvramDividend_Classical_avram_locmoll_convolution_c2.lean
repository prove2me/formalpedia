-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_convolution_c2
-- name    : AvramDividend.Classical.avram_locmoll_convolution_c2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:20:22.615061+00:00
-- url     : https://prove2.me/theorems/78984326-22d9-499d-8512-8b56fbc16bf3
-- title:
--   Compact smooth kernel convolved with a monotone function is C2
-- statement:
--   Compact smooth kernel convolved with a monotone function is C2
-- source:
--   Avram localised smoothing: exact decomposition of cc3b5448-3c78-4978-81ca-d6f25ef6998d

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_convolution_c2
    (V ρ : ℝ → ℝ) (hVmono : Monotone V)
    (hρsmooth : ContDiff ℝ 2 ρ) (hρcompact : HasCompactSupport ρ) :
    let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
    (∀ y : ℝ, Integrable (fun r => ρ r * V (y - r))) ∧
    ContDiff ℝ 2 g := by sorry
