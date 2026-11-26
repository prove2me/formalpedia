-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_weighted_jump_product
-- name    : AvramDividend.Classical.avram_locmoll_weighted_jump_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:45:47.932806+00:00
-- url     : https://prove2.me/theorems/f65151d2-2e31-5624-8ab5-d50e12992d62
-- title:
--   Product integrability of a weighted full negative-mark kernel with compact interior translates
-- statement:
--   Product integrability of a weighted full negative-mark kernel with compact interior translates
-- source:
--   Avram Proposition 4(i), child of 10e0ec45-30d2-5555-bcde-5adae9d0be9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_weighted_jump_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (V ρ : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hVmono : Monotone V) (hVnonneg : ∀ t, 0 ≤ V t)
    (hV : ContDiffOn ℝ 2 V (Ioo 0 a))
    (hρ : Integrable ρ) (hρm : Measurable ρ)
    (hs : ∀ᵐ r ∂volume, ρ r ≠ 0 → a - r ∈ Icc l u) :
    Integrable (fun p : ℝ × ℝ => ρ p.1 *
      SpectrallyNegativeLevy.generatorIntegrand V (a - p.1) p.2)
      (volume.prod (X.ν.restrict (Iio 0))) := by sorry
