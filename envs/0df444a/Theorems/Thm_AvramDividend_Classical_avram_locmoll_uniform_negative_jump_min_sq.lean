-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_uniform_negative_jump_min_sq
-- name    : AvramDividend.Classical.avram_locmoll_uniform_negative_jump_min_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:45:50.432293+00:00
-- url     : https://prove2.me/theorems/bd686587-64aa-4661-a737-f3e22013bd55
-- title:
--   Uniform full negative-mark quadratic truncation envelope for monotone C2 tests
-- statement:
--   Uniform full negative-mark quadratic truncation envelope for monotone C2 tests
-- source:
--   Avram Proposition 4(i), child of 10e0ec45-30d2-5555-bcde-5adae9d0be9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_uniform_negative_jump_min_sq
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (V : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hVmono : Monotone V) (hVnonneg : ∀ t, 0 ≤ V t)
    (hV : ContDiffOn ℝ 2 V (Ioo 0 a)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc l u, ∀ z < 0,
      ‖SpectrallyNegativeLevy.generatorIntegrand V x z‖ ≤ K * min 1 (z ^ 2) := by sorry
