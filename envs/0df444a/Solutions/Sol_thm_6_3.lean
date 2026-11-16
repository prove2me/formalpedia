-- Prove2me | solution 1 for thm_6_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:08.551197+00:00
-- url     : https://prove2.me/submissions/c61e6fe4-394f-4ff2-91bc-59d48a776424

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_3_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hXY : X ≤ Y) :
    ∫⁻ ω, X ω ∂μ ≤ ∫⁻ ω, Y ω ∂μ := by
  exact lintegral_mono hXY

